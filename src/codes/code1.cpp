#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <regex>
#include <stack>
#include <set>
#include <sstream>
using namespace std;

class CToPromelaTranslator {
private:
    static const regex mainRe;
    static const regex funcRe;
    string inputFile;
    string outputFile;
    vector<string> cCode;
    vector<string> promelaCode;
    stack<string> context;  // track contexts: if, loop, switch:<var>, struct, func, main
    bool inStructDefinition=false;
    string lastStructName;
    bool mainExists = false;
    int mainBraceCount = 0;
    set<string> functions;        // defined functions (excluding main)
    set<string> calledFunctions;  // functions called in main
    
        // ── Helpers for emitting & indentation ──────────────────────────────────────
    int indentLevel = 0;                // ← you already have this
    string currentFunc;                 // ← new: track which function we're in

    // return a string of 4×indentLevel spaces
    string indent() const {
        return string(indentLevel * 4, ' ');
    }

    // push a line to promelaCode
    void emit(const string &s) {
        promelaCode.push_back(s);
    }

    // trim whitespace
    string trim(const string &s) const {
        return regex_replace(s,
            regex(R"(^\s+|\s+$)"), "");
    }
    // ------ ADD THIS ------
            vector<string> split_on_whitespace(const string &s) {
                vector<string> toks;
                istringstream iss(s);
                string w;
                while (iss >> w) toks.push_back(w);
                return toks;
            }
            // ----------------------


    // collect enum values: read following lines until '}' and return names
    vector<string> collectEnumValues(size_t &i) {
        vector<string> vals;
        while (++i < cCode.size()) {
            string line = trim(cCode[i]);
            if (line == "};" || line == "}") break;
            // assume each line is like "RED," or "BLUE"
            auto comma = line.find(',');
            string name = (comma==string::npos ? line : line.substr(0,comma));
            vals.push_back(trim(name));
        }
        return vals;
    }

    // join ["A","B","C"] → "A, B, C"
    string join(const vector<string>& v, const string& sep) const {
        string out;
        for (size_t j = 0; j < v.size(); ++j) {
            out += v[j];
            if (j+1 < v.size()) out += sep;
        }
        return out;
    }

    // detect & extract a C return statement
    bool detectReturn(const string& l) const {
        return regex_search(l, regex(R"(^return\s+[^;]+;)"));
    }
    string extractReturnExpr(const string& l) const {
        smatch m;
        regex r(R"(^return\s+([^;]+);)");
        return (regex_search(l, m, r) ? m[1].str() : "");
    }
    // ─────────────────────────────────────────────────────────────────────────────

    // Detection functions...
    bool detectStruct(const string& line) {
        return regex_search(line, regex(R"(^struct\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*\{)"));
    }
    bool detectIf(const string& line) {
        return regex_search(line, regex(R"(^if\s*\(.*\))"));
    }
    bool detectElseIf(const string& line) {
        return regex_search(line, regex(R"(^else\s+if\s*\(.*\))"));
    }
    bool detectElse(const string& line) {
        return regex_search(line, regex(R"(^else\b)"));
    }
    bool detectWhile(const string& line) {
        return regex_search(line, regex(R"(^while\s*\(.*\))"));
    }
    bool detectFor(const string& line) {
        return regex_search(line, regex(R"(^for\s*\([^;]*;.*;.*\))"));
    }
    bool detectSwitch(const string& line) {
        return regex_search(line, regex(R"(^switch\s*\(.*\))"));
    }
    bool detectCase(const string& line) {
        return regex_search(line, regex(R"(^case\s+.*:)"));
    }
    bool detectDefault(const string& line) {
        return regex_search(line, regex(R"(^default:)"));
    }
    bool detectBreak(const string& line) {
        return regex_search(line, regex(R"(^\s*break;)"));
    }
    bool detectContinue(const string& line) {
        return regex_search(line, regex(R"(^\s*continue;)"));
    }
    bool detectFunction(const string& line) {
        return regex_search(line, funcRe);
    }
    bool detectMain(const string& line) {
        return regex_search(line, mainRe);
    }
        // ── New detection funcs ──────────────────────────────────────────────────────
    bool detectInline(const string& l) {
    return regex_search(l, regex(R"(^\s*inline\s+([A-Za-z_]\w*)\s*\(([^)]*)\)\s*\{)"));
    }
    bool detectTypedef(const string& l) {
    return regex_search(l, regex(R"(^\s*typedef\s+[A-Za-z_]\w*\s+[A-Za-z_]\w*\s*;)"));
    }
    bool detectChan(const string& l) {
    return regex_search(l, regex(R"(^\s*chan\s+\w+\s*=\s*\[\s*\d+\s*\]\s*of\s*\{)"));
    }
    bool detectAtomic(const string& l) {
    return regex_search(l, regex(R"(^\s*atomic\s*\{)"));
    }
    bool detectEnum(const string& l) {
    return regex_search(l, regex(R"(^\s*enum\s+[A-Za-z_]\w*\s*\{)"));
    }
    bool detectMalloc(const string& l) {
    return regex_search(l, regex(R"(malloc\s*\()"));
    }
    // ─────────────────────────────────────────────────────────────────────────────

public:
    CToPromelaTranslator(const string& input, const string& output)
        : inputFile(input), outputFile(output) {}

    bool run() {
        // Read input
        ifstream inFile(inputFile);
        if (!inFile.is_open()) {
            cerr << "Error: Could not open " << inputFile << endl;
            return false;
        }
        string raw;
        while (getline(inFile, raw)) cCode.push_back(raw);
        inFile.close();

        // First pass: collect functions + detect main
        for (auto& lineRaw : cCode) {
            string line = regex_replace(lineRaw, regex("^\\s+"), "");
            if (detectMain(line)) {
                mainExists = true;
            }
            else if (detectFunction(line)) {
                smatch m;
                regex re(R"(^([A-Za-z_][A-Za-z0-9_]*\s+)+([A-Za-z_][A-Za-z0-9_]*)\s*\([^)]*\)\s*\{)");
                if (regex_search(line, m, re) && m[2] != "main")
                    functions.insert(m[2]);
            }
            
        }

        // Header
        promelaCode.push_back("/* Automatically translated from C to Promela */");
        promelaCode.push_back("/* Original file: " + inputFile + " */\n");

        // Second pass
        for (size_t i = 0; i < cCode.size(); ++i) {
            string rawLine = cCode[i];
            string line = regex_replace(rawLine, regex("^\\s+"), "");
            // ── Handle new Promela constructs ────────────────────────────────────────────
            {
                static const regex globalPtrRe(
                    R"(^\s*struct\s+([A-Za-z_]\w*)\s*\*\s*(\w+);)"
                );
                smatch m;
                if (regex_match(line, m, globalPtrRe)) {
                    emit(indent() + "int " + m[2].str() + ";");
                    continue;   // skip all the later cases and the default emit
                }
            }
            {
                // matches: var->field = expr;
                static const regex ptrAssignRe(
                    R"(^\s*([A-Za-z_]\w*)->([A-Za-z_]\w*)\s*=\s*(.+);)"
                );
                smatch m;
                if (regex_match(line, m, ptrAssignRe)) {
                    string ptr   = m[1].str();             // e.g. "tail"
                    string field = m[2].str();             // e.g. "next"
                    string expr  = trim(m[3].str());       // e.g. "temp"
                    // “node” is your struct name; replace “node” if you have others
                    emit(indent() + "node_mem[" + ptr + "]." + field + " = " + expr + ";");
                    continue;
                }
            }
            // 1) inline macros → inline name(args) { … }
            if (detectInline(line)) {
            smatch m;
            regex inlineRe(R"(^\s*inline\s+([A-Za-z_]\w*)\s*\(([^)]*)\)\s*\{)");
            regex_search(line, m, inlineRe);
            emit(indent() + "inline " + m[1].str() + "(" + m[2].str() + ") {");
            context.push("inline");  indentLevel++;
            continue;
            }

            // 2) plain typedefs → echo through to Promela
            if (detectTypedef(line)) {
            emit(indent() + line);
            continue;
            }

            // 3) channel declarations → chan name = [N] of { types };
            if (detectChan(line)) {
            smatch m;
            regex chanRe(R"(^\s*chan\s+(\w+)\s*=\s*\[\s*(\d+)\s*\]\s*of\s*\{\s*([^}]+)\s*\})");
            regex_search(line, m, chanRe);
            emit(indent() + "chan " + m[1].str()
                + " = [" + m[2].str() + "] of { " + m[3].str() + " };");
            continue;
            }

            // 4) atomic blocks
            if (detectAtomic(line)) {
            emit(indent() + "atomic {");
            context.push("atomic");  indentLevel++;
            continue;
            }
            if (!context.empty() && context.top()=="atomic" && trim(line)=="}") {
            indentLevel--;
            emit(indent() + "}");
            context.pop();
            continue;
            }

            // 5) enums → mtype = { VAL1, VAL2, … };
                if (detectEnum(line)) {
                    vector<string> vals = collectEnumValues(i);
                    emit(indent() + "mtype = { " + join(vals, ", ") + " };");
                    continue;
                }


            // 6) malloc → comment or model as heap
            if (detectMalloc(line)) {
            emit(indent() + "/* heap_alloc → index */");
            continue;
            }
            // ------ ADD THIS JUST BEFORE the 'if (detectReturn(line) && currentFunc=="main")' block ------
            if (detectReturn(line) && !currentFunc.empty() && currentFunc != "main") {
                string expr = extractReturnExpr(line);
                // 1) send it on ret_<func>
                emit(indent() + "ret_" + currentFunc + "! " + expr + ";");
                // 2) jump to end label
                emit(indent() + "goto end;");
                continue;
            }


            // 7) non‐main return values → assign to ret_<func>
            // ── NEW: handle return in main ───────────────────────────────────────────────
            if (detectReturn(line) && currentFunc == "main") {
                // extract the returned expression, e.g. "test(x,y)"
                string expr = extractReturnExpr(line);
                smatch m;
                // does it look like a function-call?
                static const regex callRe(R"(^([A-Za-z_]\w*)\(([^)]*)\)$)");
                if (regex_match(expr, m, callRe)) {
                    string fn   = m[1].str();
                    string args = m[2].str(); // e.g. "x,y"

                    // 1) declare the channel and a local temp
                    emit(indent() + "chan ret_" + fn + " = [0] of { int };");
                    emit(indent() + "int tmp;");

                    // 2) run the function
                    emit(indent() + "run " + fn + "(ret_" + fn + ", " + args + ");");

                    // 3) receive its return value
                    emit(indent() + "ret_" + fn + " ? tmp;");

                    // 4) send it back to init
                    emit(indent() + "in_main ! tmp;");

                    // 5) jump to the end label
                    emit(indent() + "goto end;");

                } else {
                    // fall back to a plain return if it’s not a call
                    
                    emit(indent() + "/* unsupported return: " + expr + " */");
                }
                continue;
            }
            // ─────────────────────────────────────────────────────────────────────────────

            // ─────────────────────────────────────────────────────────────────────────────

            // special "} else {" handling  
            if (regex_search(line, regex(R"(^\}\s*else\s*\{)"))) {
                // close the previous if branch
                if (!context.empty() && context.top() == "ifThen") {
                    context.pop();
                    emit(indent()+ "fi;");
                }
                emit(indent()+ ":: else ->");
                continue;
            }


            // 1) Opening the struct: don’t print the “{”
            if (!inStructDefinition && detectStruct(line)) {
                smatch m;
                regex re(R"(^struct\s+([A-Za-z_]\w*)\s*\{)");
                regex_search(line, m, re);
                lastStructName = m[1].str();
                emit(indent() + "typedef " + lastStructName + "{");
                context.push("struct");
                inStructDefinition = true;
                indentLevel++;
                continue;
            }

            // 2) While we’re in the struct, map each field
            if (!context.empty() && context.top()=="struct") {
                // closing?
                if (regex_search(line, regex(R"(^\};|\}\s*;)"))) {
                    indentLevel--;
                    // now emit the mem/valid arrays
                    emit(indent() + "};");

                    emit(indent() + lastStructName + " " + lastStructName + "_mem[9];");
                    emit(indent() + "int " + lastStructName + "_valid[9];");
                    context.pop();
                    inStructDefinition = false;
                } else {
                    smatch m;
                    // match “struct <Name> * <field>;”
                    static const regex ptrFieldRe(R"(^\s*struct\s+[A-Za-z_]\w*\s*\*\s*(\w+);)");
                    // match “int <field>;”
                    static const regex intFieldRe(R"(^\s*int\s+(\w+);)");
                    if (regex_match(line, m, ptrFieldRe)) {
                        // pointers become plain ints
                        emit(indent() + "int " + m[1].str() + ";");
                    }
                    else if (regex_match(line, m, intFieldRe)) {
                        emit(indent() + line);
                    }
                    // else silently drop anything else
                }
                continue;
            }

            // ── Handle struct variable declarations: drop the `struct` keyword ─────────
            {
            static const regex structVarRe(
                R"(^\s*struct\s+([A-Za-z_]\w*)\s+(.+);$)"
            );
            smatch m;
            if (regex_search(line, m, structVarRe)) {
                // m[1] = type name, m[2] = rest of declaration (e.g. "n[10]")
                emit(indent() + m[1].str() + " " + m[2].str() + ";");
                continue;
            }
            }
            // ─────────────────────────────────────────────────────────────────────────────

            // non-main function definitions
            if (detectFunction(line) && !regex_search(line, regex(R"(\bmain\b)"))) {
                // 1) get the function name
                smatch m; 
                regex nameRe(R"(^\s*([A-Za-z_]\w*)\s*\()");
                regex_search(line, m, nameRe);
                currentFunc = m[1].str();

                // 2) extract the raw parameter text between parentheses
                smatch paramReMatch; 
                regex paramsRe(R"(\(\s*([^)]*)\))");
                regex_search(line, paramReMatch, paramsRe);
                string rawParams = paramReMatch[1].str();           // e.g. "struct node* temp"

                // 3) build the Promela signature pieces
                vector<string> sigParts;
                // every proctype needs its own "in" channel
                // 1) in‐channel
            sigParts.push_back("chan in " + currentFunc);

            // 2) map each C parameter "type name" → "int name"
            vector<string> params;
            stringstream ss(rawParams);
            string p;
            while (getline(ss, p, ',')) {
                // trim p, then split on space to grab the identifier
                p = trim(p);
                auto toks = split_on_whitespace(p);
                if (toks.size() >= 2) {
                    string name = toks.back();       // last token is the param name
                    params.push_back("int " + name);
                }
            }
            for (auto &pr : params)
                sigParts.push_back(pr);

                            
                // if there's exactly one struct-pointer parameter, map to an int
                smatch paramM;
                static const regex ptrParamRe(R"(struct\s+[A-Za-z_]\w*\s*\*\s*(\w+))");
                if (regex_search(rawParams, paramM, ptrParamRe)) {
                    sigParts.push_back("int " + paramM[1].str());
                }

                // 4) join them: "chan in test; int temp"
                // ------ REPLACE WITH THIS ------
                string signature = join(sigParts, "; ");

                // 5) emit the proctype with that signature
                emit(indent() + "proctype " + currentFunc + "(" + signature + ") {");
                indentLevel++;                                    // enter proctype body
                emit(indent() + "chan ret_" + currentFunc + " = [0] of { int };");
                emit(indent() + "int tmp;");
                context.push("func");
                continue;

            }


            // entering main
                        // entering main
               if (detectMain(line)) {
                    currentFunc = "main";
                    // main now takes its own return channel
                    emit(indent() + "proctype main(chan ret_main) {");
                    context.push("main");
                    indentLevel++;
                    continue;
                }



            // —— Standalone “inside main” logic —— 
            // (updates brace count and collects called functions, but DOESN’T eat the line)
            if (!context.empty() && context.top() == "main" && regex_search(line, regex(R"(^return\s+0\s*;)")))
            {
                continue;
            }
            if (!context.empty() && context.top() == "main") {
                if (line.find("{") != string::npos) mainBraceCount++;
                if (line.find("}") != string::npos) mainBraceCount--;
                smatch m;
                regex callRe(R"(([A-Za-z_][A-Za-z0-9_]*)\s*\([^;]*\)\s*;)");
                if (regex_search(line, m, callRe) && functions.count(m[1].str()))
                    calledFunctions.insert(m[1].str());
                if (mainBraceCount == 0) {
                    indentLevel--;
                    context.pop();
                }
            }


                        // —— New: catch single‐line `if(cond) stmt;` + next‐line `else stmt;` ——
            {
                // 1) does this line look like “if(cond) thenStmt;” ?
                static const std::regex singleIfRe(
                    R"(^\s*if\s*\(([^)]+)\)\s*([^;]+);$)"
                );
                std::smatch m1;
                if (std::regex_match(line, m1, singleIfRe)
                    && i + 1 < cCode.size()  // there *is* a next line
                ) {
                    // 2) peek at the next line
                    string nextRaw = cCode[i+1];
                    string next    = regex_replace(nextRaw, regex("^\\s+"), "");
                    static const std::regex elseRe(
                        R"(^else\s+([^;]+);)"
                    );
                    std::smatch m2;
                    if (std::regex_match(next, m2, elseRe)) {
                        // we’ve got both parts: emit Promela “do…od”
                        string cond     = trim(m1[1].str());
                        string thenStmt = trim(m1[2].str());
                        string elseStmt = trim(m2[1].str());
                        emit(indent() + "if");
                        emit(indent() + "    :: (" + cond + ") -> " + thenStmt + ";");
                        emit(indent() + "    :: else -> " + elseStmt + ";");
                        emit(indent() + "fi");
                        // skip the next line so it isn’t emitted again
                        ++i;
                        continue;
                    }
                }
            }



            // --- NEW: handle braced if/else in one line ---
            static const std::regex bracedIfElseRe(
                R"(^\s*if\s*\(([^)]+)\)\s*\{\s*([^}]+)\s*\}\s*else\s*\{\s*([^}]+)\s*\})"
            );
            std::smatch mBr;
            if (std::regex_match(line, mBr, bracedIfElseRe)) {
                auto cond     = trim(mBr[1].str());
                auto thenStmt = trim(mBr[2].str());
                auto elseStmt = trim(mBr[3].str());

                emit(indent() + "if");
                emit(indent() + "    :: (" + cond + ") -> " + thenStmt + ";");
                emit(indent() + "    :: else    -> " + elseStmt + ";");
                emit(indent() + "fi");
                continue;
            }

            static const std::regex inlineIfElseRe(
                R"(^\s*if\s*\(([^)]+)\)\s*([^;]+);\s*else\s*([^;]+);)"
            );
            std::smatch mInLine;
            if (std::regex_match(line, mInLine, inlineIfElseRe)) {
                auto cond     = trim(mInLine[1].str());
                auto thenStmt = trim(mInLine[2].str());
                auto elseStmt = trim(mInLine[3].str());

                emit(indent() + "do");
                emit(indent() + "    :: (" + cond + ") -> " + thenStmt + ";");
                emit(indent() + "    :: else -> " + elseStmt + ";");
                emit(indent() + "od");
                continue;
            }
            // --- end insertion ---

            if (detectElseIf(line)) {
                smatch m; regex re(R"(^else\s+if\s*\((.*)\))");
                regex_search(line, m, re);
                emit(indent() + "    :: (" + m[1].str() + ") ->");
                continue;
            }
            if (detectElse(line)) {
                emit(indent() + "    :: else ->");
                continue;
            }
            // match lines like "while (foo) {"
            static const std::regex whileWithBraceRe(R"(^\s*while\s*\((.*)\)\s*\{)");
            // …
            smatch m;
            if (std::regex_match(line, m, whileWithBraceRe)) {
                // emit the Promela loop header, but do not re-emit the '{'
                emit(indent() + "do");
                emit(indent() + "    :: (" + trim(m[1].str()) + ") ->");
                context.push("loop");
                continue;
            }

                if (detectFor(line)) {
                    // emit the Promela loop header
                    emit(indent() + "do");
            
                    // capture exactly what's between the 2nd and 3rd semicolons, up to the ')'
                    //  ^ skip init:   [^;]*;
                    //  ^ skip condition capture:  ([^;]+);
                    //  ^ skip increment: [^)]*\)
                    smatch m;
                    static const regex forCondRe(
                        R"(^\s*for\s*\(\s*[^;]*;\s*([^;]+)\s*;\s*[^)]*\))"
                    );
            
                    if (regex_search(line, m, forCondRe)) {
                        string cond = trim(m[1].str());
                        emit(indent() + "    :: (" + cond + ") ->");
                    } else {
                        // fallback if the C is malformed or conditionless
                        emit(indent() + "    :: (true) ->");
                    }
            
                    context.push("loop");
                    continue;
                }
            if (detectSwitch(line)) {
                smatch m; regex re(R"(^switch\s*\((.*)\))");
                regex_search(line, m, re);
                emit(indent() + "if");
                context.push("switch:" + m[1].str());
                continue;
            }
            if (detectCase(line)) {
                smatch m; regex re(R"(^case\s+(.*):)");
                regex_search(line, m, re);
                string var = context.top().substr(7);
                emit(indent() + "    :: (" + var + " == " + m[1].str() + ") ->");
                continue;
            }
            if (detectDefault(line)) {
                emit(indent() + "    :: else ->");
                continue;
            }
            if (detectBreak(line)) {
                emit(indent() + "    break;");
                continue;
            }
            if (detectContinue(line)) {
                emit(indent() + "    skip;");
                continue;
            }
            if (line == "}") {
                if (!context.empty()) {
                    string top = context.top();
                    if (top == "ifThen") {
                        context.pop();
                    }
                    else if (top == "if" || top.rfind("switch:",0)==0) {
                        emit(indent() + "fi;");
                        context.pop();
                    }
                    else if (top == "loop") {
                        emit(indent() + "    :: else -> break;");
                        emit(indent() + "od;");
                        context.pop();
                    }
                    else if (top == "func") {
                    // 1) declare the perpetual end‐loop
                    emit(indent() + "end:");
                    emit(indent() + "    goto end;");
                    // 2) close the proctype
                    if (currentFunc == "main") {
                        emit(indent() + "    ret_main ! 0;");
                    }

                    indentLevel--;
                    emit(indent() + "}");
                    context.pop();
                }

                }
                // catch-all: emit any unmatched '}' (e.g. closing main)
                emit(indent() + "}");
                if (!context.empty()) context.pop();
                continue;
            }
            
            
            // ── Translate ternary operator: a = (cond) ? b : c; ──────────────────────
            {
                static const regex ternaryRe(R"(^\s*(\w+)\s*=\s*\(([^)]+)\)\s*\?\s*([^:]+)\s*:\s*(.+);$)");
                smatch m;
                if (regex_match(line, m, ternaryRe)) {
                    string lhs      = trim(m[1]);
                    string cond     = trim(m[2]);
                    string trueExpr = trim(m[3]);
                    string falseExpr= trim(m[4]);

                    emit(indent() + "if");
                    emit(indent() + "    :: (" + cond + ") -> " + lhs + " = " + trueExpr + ";");
                    emit(indent() + "    :: else -> " + lhs + " = " + falseExpr + ";");
                    emit(indent() + "fi;");
                    continue;
                }
            }
            // ─────────────────────────────────────────────────────────────────────────
            // default: emit the line as-is (with indentation)
            
            emit(indent() + line);
        }
        // wrap up with init { run main(); … }
            if (mainExists) {
                promelaCode.push_back("");
                promelaCode.push_back("init {");
                promelaCode.push_back("    chan ret_main = [0] of { bit };");
                promelaCode.push_back("    run main(ret_main);");
                promelaCode.push_back("    ret_main?0;");
                promelaCode.push_back("}");
            }

        // write out
        ofstream out(outputFile);
        if (!out.is_open()) {
            cerr << "Error: Could not open " << outputFile << endl;
            return false;
        }
        for (auto& l : promelaCode) out << l << "\n";
        return true;
    }
};
//— define our regex patterns just once, outside the class body —
const std::regex CToPromelaTranslator::funcRe(
    R"(^\s*([A-Za-z_][A-Za-z0-9_]*\s*(\*+)?\s+)+([A-Za-z_][A-Za-z0-9_]*)\s*\([^)]*\)\s*\{)"
);
const std::regex CToPromelaTranslator::mainRe(
    R"(^\s*(?:int|void)\s+main\s*\(\s*(?:void)?\s*\)\s*\{)"
);


int main(int argc, char* argv[]) {
    string in = "input.c", out = "output1.pml";
    if (argc>1) in = argv[1];
    if (argc>2) out = argv[2];
    CToPromelaTranslator T(in, out);
    return T.run() ? 0 : 1;
}
