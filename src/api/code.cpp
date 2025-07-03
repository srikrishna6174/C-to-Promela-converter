#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <regex>
#include <stack>
#include <set>

using namespace std;

class CToPromelaTranslator {
private:
    string inputFile;
    string outputFile;
    vector<string> cCode;
    vector<string> promelaCode;
    stack<string> context;  // track contexts: if, loop, switch:<var>, struct, func, main
    bool inStructDefinition = false;
    int indentLevel = 0;
    bool mainExists = false;
    int mainBraceCount = 0;
    set<string> functions;        // defined functions (excluding main)
    set<string> calledFunctions;  // functions called in main

    // Detection functions for various C constructs
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
        // Matches a function definition (return type + name + parameters + '{')
        return regex_search(line, regex(R"(^([A-Za-z_][A-Za-z0-9_]*\s+)+([A-Za-z_][A-Za-z0-9_]*)\s*\([^;]*\)\s*\{)"));
    }
    bool detectMain(const string& line) {
        return regex_search(line, regex(R"(^.*\bmain\s*\(.*\))"));
    }

public:
    CToPromelaTranslator(const string& input, const string& output)
        : inputFile(input), outputFile(output) {}

    bool run() {
        // Read all lines of the C input
        ifstream inFile(inputFile);
        if (!inFile.is_open()) {
            cerr << "Error: Could not open input file " << inputFile << endl;
            return false;
        }
        string line;
        while (getline(inFile, line)) {
            cCode.push_back(line);
        }
        inFile.close();

        // First pass: record all function names (except main) and detect if main exists
        for (auto& rawLine : cCode) {
            string lineTrim = regex_replace(rawLine, regex("^\\s+"), "");
            if (detectFunction(lineTrim)) {
                smatch m;
                regex re(R"(^([A-Za-z_][A-Za-z0-9_]*\s+)+([A-Za-z_][A-Za-z0-9_]*)\s*\([^)]*\)\s*\{)");
                if (regex_search(lineTrim, m, re)) {
                    string funcName = m[2].str();
                    if (funcName != "main") {
                        functions.insert(funcName);
                    }
                }
            }
            else if (detectMain(lineTrim)) {
                mainExists = true;
            }
        }

        // Header comments
        promelaCode.push_back("/* Automatically translated from C to Promela */");
        promelaCode.push_back("/* Original file: " + inputFile + " */");
        promelaCode.push_back("");

        // Second pass: process each line and translate
        for (auto& rawLine : cCode) {
            string line = regex_replace(rawLine, regex("^\\s+"), "");

            // Struct definition
            if (!inStructDefinition && detectStruct(line)) {
                smatch m;
                regex re(R"(^struct\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*\{)");
                if (regex_search(line, m, re)) {
                    string structName = m[1].str();
                    promelaCode.push_back(string(indentLevel*4, ' ') + "typedef " + structName + " {");
                } else {
                    promelaCode.push_back(string(indentLevel*4, ' ') + line);
                }
                context.push("struct");
                inStructDefinition = true;
                indentLevel++;
            }
            else if (!context.empty() && context.top() == "struct") {
                // Inside struct definition: close it or output members
                if (regex_search(line, regex(R"(^};)")) || regex_search(line, regex(R"(^}\s*;)"))) {
                    indentLevel--;
                    promelaCode.push_back(string(indentLevel*4, ' ') + "};");
                    context.pop();
                    inStructDefinition = false;
                } else {
                    promelaCode.push_back(string(indentLevel*4, ' ') + line);
                }
            }
            // Function (non-main) definition
            else if (detectFunction(line) && !regex_search(line, regex(R"(\bmain\b)"))) {
                smatch m;
                regex re(R"(^([A-Za-z_][A-Za-z0-9_]*\s+)+([A-Za-z_][A-Za-z0-9_]*)\s*\([^)]*\)\s*\{)");
                if (regex_search(line, m, re)) {
                    string funcName = m[2].str();
                    promelaCode.push_back(string(indentLevel*4, ' ') + "proctype " + funcName + "() {");
                    context.push("func");
                    indentLevel++;
                } else {
                    promelaCode.push_back(string(indentLevel*4, ' ') + line);
                }
            }
            // Main function: enter context but do not output as a proctype
            else if (detectMain(line)) {
                context.push("main");
                indentLevel++;
                if (line.find("{") != string::npos) {
                    mainBraceCount = 1;
                }
            }
            // Inside main: collect called functions and detect end of main
            else if (!context.empty() && context.top() == "main") {
                if (line.find("{") != string::npos) {
                    mainBraceCount++;
                }
                if (line.find("}") != string::npos) {
                    mainBraceCount--;
                }
                // Detect function calls in main (e.g., foo();)
                smatch m;
                regex callRe(R"(([A-Za-z_][A-Za-z0-9_]*)\s*\([^;]*\)\s*;)");
                if (regex_search(line, m, callRe)) {
                    string called = m[1].str();
                    if (functions.count(called)) {
                        calledFunctions.insert(called);
                    }
                }
                if (mainBraceCount == 0) {
                    indentLevel--;
                    context.pop();
                }
            }
            // If/Else logic
            else if (detectIf(line)) {
                promelaCode.push_back(string(indentLevel*4, ' ') + "if");
                smatch m;
                regex re(R"(^if\s*\((.*)\))");
                if (regex_search(line, m, re)) {
                    string cond = m[1].str();
                    promelaCode.push_back(string(indentLevel*4, ' ') + "    :: (" + cond + ") ->");
                }
                context.push("if");
            }
            else if (detectElseIf(line)) {
                smatch m;
                regex re(R"(^else\s+if\s*\((.*)\))");
                if (regex_search(line, m, re)) {
                    string cond = m[1].str();
                    promelaCode.push_back(string(indentLevel*4, ' ') + "    :: (" + cond + ") ->");
                }
            }
            else if (detectElse(line)) {
                promelaCode.push_back(string(indentLevel*4, ' ') + "    :: else ->");
            }
            // While loop
            else if (detectWhile(line)) {
                promelaCode.push_back(string(indentLevel*4, ' ') + "do");
                smatch m;
                regex re(R"(^while\s*\((.*)\))");
                if (regex_search(line, m, re)) {
                    string cond = m[1].str();
                    promelaCode.push_back(string(indentLevel*4, ' ') + "    :: (" + cond + ") ->");
                }
                context.push("loop");
            }
            // For loop
            else if (detectFor(line)) {
                promelaCode.push_back(string(indentLevel*4, ' ') + "do");
                smatch m;
                // Extract the loop condition (second expression in for)
                regex re(R"(^for\s*\([^;]*;\s*([^;]*);)");
                if (regex_search(line, m, re)) {
                    string cond = m[1].str();
                    if (cond.empty()) cond = "true";
                    promelaCode.push_back(string(indentLevel*4, ' ') + "    :: (" + cond + ") ->");
                }
                context.push("loop");
            }
            // Switch-case
            else if (detectSwitch(line)) {
                smatch m;
                regex re(R"(^switch\s*\((.*)\))");
                if (regex_search(line, m, re)) {
                    string var = m[1].str();
                    promelaCode.push_back(string(indentLevel*4, ' ') + "if");
                    context.push("switch:" + var);
                }
            }
            else if (detectCase(line)) {
                smatch m;
                regex re(R"(^case\s+(.*):)");
                if (regex_search(line, m, re)) {
                    string val = m[1].str();
                    string top = context.top();
                    if (top.rfind("switch:", 0) == 0) {
                        string var = top.substr(7);
                        promelaCode.push_back(string(indentLevel*4, ' ') + "    :: (" + var + " == " + val + ") ->");
                    }
                }
            }
            else if (detectDefault(line)) {
                promelaCode.push_back(string(indentLevel*4, ' ') + "    :: else ->");
            }
            // Break/continue
            else if (detectBreak(line)) {
                promelaCode.push_back(string(indentLevel*4, ' ') + "    break;");
            }
            else if (detectContinue(line)) {
                promelaCode.push_back(string(indentLevel*4, ' ') + "    skip;");
            }
            // Closing brace of a block
            else if (line == "}") {
                if (!context.empty()) {
                    string top = context.top();
                    if (top == "if") {
                        promelaCode.push_back(string(indentLevel*4, ' ') + "fi;");
                        context.pop();
                    } else if (top.rfind("switch:", 0) == 0) {
                        promelaCode.push_back(string(indentLevel*4, ' ') + "fi;");
                        context.pop();
                    } else if (top == "loop") {
                        promelaCode.push_back(string(indentLevel*4, ' ') + "    :: else -> break;");
                        promelaCode.push_back(string(indentLevel*4, ' ') + "od;");
                        context.pop();
                    } else if (top == "func") {
                        indentLevel--;
                        promelaCode.push_back(string(indentLevel*4, ' ') + "}");
                        context.pop();
                    }
                    // The 'main' context end is handled above
                }
            }
            // Default: regular code (e.g. assignments, printf, etc.)
            else {
                promelaCode.push_back(string(indentLevel*4, ' ') + line);
            }
        }

        // Add init block to run the processes called by main
        if (mainExists) {
            promelaCode.push_back("");
            promelaCode.push_back("init {");
            for (const auto& funcName : calledFunctions) {
                promelaCode.push_back("    run " + funcName + "();");
            }
            promelaCode.push_back("}");
        }

        // Write output file
        ofstream outFile(outputFile);
        if (!outFile.is_open()) {
            cerr << "Error: Could not open output file " << outputFile << endl;
            return false;
        }
        for (const auto& ln : promelaCode) {
            outFile << ln << endl;
        }
        outFile.close();

        return true;
    }
};

int main(int argc, char* argv[]) {
    string input = "input.c";
    string output = "output.pml";
    if (argc > 1) input = argv[1];
    if (argc > 2) output = argv[2];
    CToPromelaTranslator translator(input, output);
    return translator.run() ? 0 : 1;
}
