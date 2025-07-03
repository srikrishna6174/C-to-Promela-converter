#!/usr/bin/env python3
import sys
from pycparser import parse_file, c_ast

class CtoPromelaVisitor(c_ast.NodeVisitor):
    def __init__(self):
        self.output       = []
        self.indent       = 0
        # struct name → { 'ast': c_ast.Struct, 'has_ptr': bool }
        self.structs      = {}
        self.var_types    = {}    # var name → ('ptr', struct_name)
        self.current_func = None
        self.pool_size    = 9
        self.func_names   = []    # all defined functions
        self.func_returns = {}    # func name → 'void' or 'int'
        self.tmp_defs = []    # names to declare
        self.tmp_use  = []    # names to consume when emitting

    def _scan_for_tmps(self, node):
        class Scanner(c_ast.NodeVisitor):
            def __init__(self, outer): 
                self.outer = outer
            def visit_Return(self, ret):
                # detect fib(n-1)+fib(n-2)-style returns
                e = ret.expr
                if (isinstance(e, c_ast.BinaryOp) and e.op == '+'
                    and isinstance(e.left,  c_ast.FuncCall)
                    and isinstance(e.right, c_ast.FuncCall)
                    and e.left.name.name == e.right.name.name
                    and e.left.name.name == self.outer.current_func):
                    # for each subcall we need one tmp
                    for _ in (0,1):
                        name = f"tmp_{len(self.outer.tmp_defs)}"
                        self.outer.tmp_defs.append(name)
                # no generic calls counted here
        Scanner(self).visit(node)


    def writeln(self, line=''):
        self.output.append('    ' * self.indent + line)

    def _collect_called_funcs(self, node):
        class CallCollector(c_ast.NodeVisitor):
            def __init__(self, outer):
                self.outer = outer
                self.calls = set()
            def visit_FuncCall(self, n):
                if isinstance(n.name, c_ast.ID):
                    nm = n.name.name
                    if nm in self.outer.func_returns and self.outer.func_returns[nm] != 'void':
                        self.calls.add(nm)
                self.generic_visit(n)
        collector = CallCollector(self)
        collector.visit(node)
        return collector.calls

    def visit_FileAST(self, node):
        # 0) Collect function names & return types
        for ext in node.ext or []:
            if isinstance(ext, c_ast.FuncDef):
                name = ext.decl.name
                ret  = ext.decl.type.type
                if (isinstance(ret, c_ast.TypeDecl)
                    and isinstance(ret.type, c_ast.IdentifierType)
                    and 'void' in ret.type.names):
                    self.func_returns[name] = 'void'
                else:
                    self.func_returns[name] = 'int'
        self.func_names = list(self.func_returns.keys())

        # 1) Struct typedefs
        for ext in node.ext or []:
            if isinstance(ext, c_ast.Decl) and isinstance(ext.type, c_ast.Struct):
                self._emit_struct_typedef(ext.type)

        # 2) Memory pools & valids only for structs with pointers
        for name, info in self.structs.items():
            if info['has_ptr']:
                self.writeln(f"{name} {name}_mem[{self.pool_size}];")
                self.writeln(f"int {name}_valid[{self.pool_size}];")
        self.writeln('')

        # 3) Globals
        for ext in node.ext or []:
            if (isinstance(ext, c_ast.Decl)
                and not ext.funcspec
                and not isinstance(ext.type, c_ast.Struct)):
                self._emit_global_decl(ext)
        self.writeln('')

        # 4) Functions
        for ext in node.ext or []:
            if isinstance(ext, c_ast.FuncDef):
                self.visit(ext)

        # 5) init to launch main
        if 'main' in self.func_names:
            self.writeln('init {')
            self.indent += 1
            self.writeln('chan ret_main = [0] of { int };')
            self.writeln('run main(ret_main);')
            self.writeln('ret_main ? 0;')
            self.indent -= 1
            self.writeln('}')

        return '\n'.join(self.output)

    def _emit_struct_typedef(self, struct):
        name = struct.name
        # detect if any field is a pointer
        has_ptr = False
        for fld in struct.decls or []:
            if isinstance(fld.type, c_ast.PtrDecl):
                has_ptr = True
                break

        # record struct AST and pointer‐flag
        self.structs[name] = { 'ast': struct, 'has_ptr': has_ptr }

        # emit Promela typedef
        self.writeln(f"typedef {name} " + "{")
        self.indent += 1
        for fld in struct.decls or []:
            # flatten pointer fields to int index
            if isinstance(fld.type, c_ast.PtrDecl):
                self.writeln(f"int {fld.name};")
            else:
                self.writeln(f"int {fld.name};")
        self.indent -= 1
        self.writeln("};")
        self.writeln('')

    def _emit_global_decl(self, decl):
        if isinstance(decl.type, c_ast.PtrDecl):
            base = self._extract_ptr_base(decl.type)
            if base:
                self.var_types[decl.name] = ('ptr', base)
        if isinstance(decl.type, c_ast.ArrayDecl):
            sz = self._expr(decl.type.dim)
            self.writeln(f"int {decl.name}[{sz}];")
        else:
            init = f"={self._expr(decl.init)}" if decl.init else ''
            self.writeln(f"int {decl.name}{init};")

    def _emit_local_decl(self, node):
        # record local pointer var
        if isinstance(node.type, c_ast.PtrDecl):
            base = self._extract_ptr_base(node.type)
            if base:
                self.var_types[node.name] = ('ptr', base)

        # malloc special case
        if node.init and isinstance(node.init, c_ast.FuncCall) and node.init.name.name == 'malloc':
            struct_name = self._get_sizeof_struct_name(node.init.args.exprs[0])
            self._emit_malloc(node.name, struct_name)
            return

        # arrays vs scalars
        if isinstance(node.type, c_ast.ArrayDecl):
            sz   = self._expr(node.type.dim)
            init = f" = {self._expr(node.init)}" if node.init else ''
            self.writeln(f"int {node.name}[{sz}]{init};")
        else:
            val = f" = {self._expr(node.init)}" if node.init else ''
            self.writeln(f"int {node.name}{val};")

    def visit_FuncDef(self, node):
        name = node.decl.name
        self.current_func = name

        # 0) reset tmp-tracking for this function
        self.tmp_defs.clear()
        self.tmp_use .clear()

        # 1) pointer-parameter bookkeeping (unchanged)
        params = []
        if isinstance(node.decl.type, c_ast.FuncDecl) and node.decl.type.args:
            params = node.decl.type.args.params
            for p in params:
                if isinstance(p.type, c_ast.PtrDecl):
                    base = self._extract_ptr_base(p.type)
                    if base:
                        self.var_types[p.name] = ('ptr', base)

        # 2) pre-scan body for exactly the needed tmp___* names
        self._scan_for_tmps(node.body)

        # 3) emit proctype signature
        parts = [f"chan in_{name}"] + [f"int {p.name}" for p in params]
        sig   = ';'.join(parts)
        self.writeln(f"proctype {name}({sig}) " + "{")
        self.indent += 1

        # 4) emit return-channels + generic tmp for any non-void calls
        called = self._collect_called_funcs(node.body)
        for callee in sorted(called):
            self.writeln(f"chan ret_{callee} = [0] of {{ int }};")
            self.writeln("int tmp;")

        # 5) emit exactly the tmp___* you discovered
        for t in self.tmp_defs:
            self.writeln(f"int {t};")
        self.writeln("")   # blank line before body

        # prepare tmp_use as a FIFO queue
        self.tmp_use = list(self.tmp_defs)

        # 6) emit the body
        self._visit_compound(node.body)
        self.writeln("")

        # 7) void-return stub, if required
        if self.func_returns[name] == 'void':
            self.writeln(f"in_{name}!0;")
            self.writeln("goto end;")

        # 8) epilogue
        self.indent -= 1
        self.writeln("end:")
        self.indent += 1
        self.writeln(f'printf("End of {name}\\n");')
        self.indent -= 1
        self.writeln("}")
        self.writeln("")

        self.current_func = None

    def _visit_compound(self, node):
        for stmt in node.block_items or []:
            if isinstance(stmt, c_ast.Decl):
                self._emit_local_decl(stmt)
        # NEW —- handle “bare” expressions (e.g. free(new);)
            elif isinstance(stmt, c_ast.FuncCall):
                self.visit(stmt)
            else:
                self.visit(stmt)
                
    def _emit_malloc(self, var, struct_name):
        malloc_var = f"malloc_{struct_name}_c"
        self.writeln(f"int {malloc_var};")
        self.writeln(f"int {var};")
        self.writeln("int tmp;")
        self.writeln("atomic {")
        self.indent += 1
        self.writeln(f"{malloc_var} = 1;")
        self.writeln("do")
        self.indent += 1
        self.writeln(f":: ({malloc_var} >= {self.pool_size}) -> break;")
        self.writeln(":: else ->")
        self.indent += 1
        self.writeln("if")
        self.indent += 1
        self.writeln(f":: ({struct_name}_valid[{malloc_var}] == 0) ->")
        self.indent += 1
        self.writeln(f"{struct_name}_valid[{malloc_var}] = 1;")
        self.writeln("break;")
        self.indent -= 1
        self.writeln(f":: else -> {malloc_var}++;")
        self.indent -= 1
        self.writeln("fi;")
        self.indent -= 1
        self.writeln("od;")
        self.writeln(f"assert({malloc_var} < {self.pool_size});")
        self.writeln(f"tmp = {malloc_var};")
        self.indent -= 1
        self.writeln("};")
        self.writeln(f"{var} = tmp;")
        
    def visit_Assignment(self, node):
        # ── 0) Handle chained a = b = c; ──
        if isinstance(node.rvalue, c_ast.Assignment):
            inner = node.rvalue
            # first do the inner b = c
            self.visit_Assignment(inner)
            # then do a = b
            outer_lhs = self._expr(node.lvalue)
            inner_lhs = self._expr(inner.lvalue)
            self.writeln(f"{outer_lhs} = {inner_lhs};")
            return

        # ── 1) detect x = x + 1  or  x = 1 + x  → x++; ──
        if (isinstance(node.lvalue, c_ast.ID)
            and isinstance(node.rvalue, c_ast.BinaryOp)
            and node.rvalue.op in ('+','-')):
            lv = node.lvalue.name
            op = node.rvalue.op
            L, R = node.rvalue.left, node.rvalue.right
            def is_self_inc(left, right):
                return (isinstance(left, c_ast.ID)
                        and isinstance(right, c_ast.Constant)
                        and left.name == lv and right.value == '1')
            if is_self_inc(L, R) or is_self_inc(R, L):
                self.writeln(f"{lv}{'++' if op=='+' else '--'};")
                return

        # ── 2) ternary: cond ? a : b ──
        if isinstance(node.rvalue, c_ast.TernaryOp):
            lhs  = self._expr(node.lvalue)
            cond = self._expr(node.rvalue.cond)
            tru  = self._expr(node.rvalue.iftrue)
            fls  = self._expr(node.rvalue.iffalse)
            self.writeln("if")
            self.indent += 1
            self.writeln(f":: ({cond}) -> {lhs} = {tru};")
            self.writeln(":: else ->")
            self.writeln(f"   {lhs} = {fls};")
            self.indent -= 1
            self.writeln("fi;")
            return

        # ── 3) x = fn(...); for int‐returning fn ──
        if isinstance(node.rvalue, c_ast.FuncCall):
            callee = node.rvalue.name.name
            if callee in self.func_returns and self.func_returns[callee] != 'void':
                lhs  = self._expr(node.lvalue)
                args = ','.join(self._expr(a)
                                for a in (node.rvalue.args.exprs or []))
                self.writeln(f"run {callee}(ret_{callee}"
                              f"{',' if args else ''}{args});")
                self.writeln(f"ret_{callee} ? {lhs};")
                return

        # ── 4) fallback: simple assignment ──
        lhs = self._expr(node.lvalue)
        rhs = self._expr(node.rvalue)
        self.writeln(f"{lhs} = {rhs};")

    
    def visit_BinaryOp(self, node):
        # emit a bare binary‐operator expression as-is
        self.writeln(f"{self._expr(node)};")
    def visit_UnaryOp(self, node):
        op = node.op
        if op in ('p++', 'p--', '++', '--'):
            var = self._expr(node.expr)
            self.writeln(f"{var} = {var} {'+ 1' if '++' in op else '- 1'};")
        else:
            self.writeln(f"{self._expr(node)};")

    def visit_If(self, node):
        cond = self._expr(node.cond)
        self.writeln("if")
        self.indent += 1
        self.writeln(f":: ({cond}) ->")
        self.indent += 1
        self.visit(node.iftrue)
        self.indent -= 1
        if node.iffalse:
            self.writeln(":: else ->")
            self.indent += 1
            self.visit(node.iffalse)
            self.indent -= 1
        self.indent -= 1
        self.writeln("fi;")

    def visit_For(self, node):
    # Emit initialization part (e.g., i = 1)
        if node.init:
            if isinstance(node.init, c_ast.Decl):
                self._emit_local_decl(node.init)
            else:
                self.visit(node.init)

        self.writeln("do")
        self.indent += 1
    # Emit conditional guard
        if node.cond:
            cond = self._expr(node.cond)
            self.writeln(f":: !({cond}) -> break")
            self.writeln(f":: ({cond}) -> {{")
        else:
            self.writeln(":: else -> {")

        self.indent += 1
    # Emit loop body
        self.visit(node.stmt)
    # Emit increment part (e.g., i++)
        if node.next:
            if isinstance(node.next, c_ast.ExprList):
                for expr in node.next.exprs:
                    self.visit(expr)
            else:
                self.visit(node.next)
        self.indent -= 1
        self.writeln("}")
        self.indent -= 1
        self.writeln("od")
    def visit_While(self, node):
        self._loop(node)
    def visit_DoWhile(self, node):
        self._loop(node)

    def _loop(self, node):
        cond = getattr(node, 'cond', None)
        cs   = self._expr(cond) if cond else ''
        self.writeln("do")
        self.indent += 1
        if cs:
            self.writeln(f":: ({cs}) -> {{")
            self.indent += 1
            self.visit(node.stmt)
            self.indent -= 1
            self.writeln("}")
        else:
            self.writeln(":: else -> {")
            self.indent += 1
            self.visit(node.stmt)
            self.indent -= 1
            self.writeln("}")
        self.indent -= 1
        self.writeln("od;")

    def visit_Break(self, node):
        self.writeln("break;")
    def visit_Continue(self, node):
        self.writeln("continue;")
    def visit_Goto(self, node):
        # CIL: goto target;    →   Promela: goto target;
        self.writeln(f"goto {node.name};")
    def visit_Label(self, node):
        # CIL: label: stmt;    →   Promela: label:  \n    <stmt>
        self.writeln(f"{node.name}:")
        # emit the labeled statement itself
        self.indent += 1
        self.visit(node.stmt)
        self.indent -= 1
    def visit_FuncCall(self, node):
        nm = node.name.name
        # free()
        if nm == 'free':
            ptr = self._expr(node.args.exprs[0])
            vt  = self.var_types.get(ptr)
            if vt and vt[0] == 'ptr':
                struct = vt[1]
                self.writeln("d_step {")
                self.indent += 1
                self.writeln(f"{struct}_valid[{ptr}] = 0;")
                for fld in self.structs[struct]['ast'].decls or []:
                    self.writeln(f"{struct}_mem[{ptr}].{fld.name} = 0;")
                self.indent -= 1
                self.writeln("};")
            return

        args = [self._expr(a) for a in (node.args.exprs if node.args else [])]
        arg_str = ','.join(args)
        if nm in self.func_returns and self.func_returns[nm] != 'void':
            self.writeln(f"run {nm}(ret_{nm}{',' if arg_str else ''}{arg_str});")
        else:
            self.writeln(f"run {nm}({arg_str});")
    def visit_Switch(self, node):
        expr = self._expr(node.cond)
        # group cases/defaults
        groups = []  # list of (label, [stmts])
        cur_label = None
        for item in node.stmt.block_items or []:
            if isinstance(item, c_ast.Case):
                cur_label = self._expr(item.expr)
                groups.append((cur_label, list(item.stmts)))
            elif isinstance(item, c_ast.Default):
                cur_label = 'else'
                groups.append((cur_label, list(item.stmts)))
            else:
                # continuation of last group
                if groups:
                    groups[-1][1].append(item)
        # emit Promela if
        self.writeln("if")
        self.indent += 1
        for label, stmts in groups:
            if label == 'else':
                self.writeln(":: else ->")
            else:
                self.writeln(f":: ({expr} == {label})->")
            self.indent += 1
            for s in stmts:
                self.visit(s)
            self.indent -= 1
        self.indent -= 1
        self.writeln("fi")
        
    def visit_Return(self, node):
        # skip void returns
        if self.func_returns[self.current_func] == 'void':
            return

        e = node.expr

        # special-case recursive f(...) + f(...)
        if (isinstance(e, c_ast.BinaryOp) and e.op == '+'
            and isinstance(e.left,  c_ast.FuncCall)
            and isinstance(e.right, c_ast.FuncCall)
            and e.left.name.name == self.current_func):

            # pull exactly two temps from tmp_use
            tmp1 = self.tmp_use.pop(0)
            tmp2 = self.tmp_use.pop(0)

            # first recursive call
            args1 = ','.join(self._expr(a) for a in e.left.args.exprs)
            self.writeln(f"run {self.current_func}(ret_{self.current_func}, {args1});")
            self.writeln(f"ret_{self.current_func} ? {tmp1};")

            # second recursive call
            args2 = ','.join(self._expr(a) for a in e.right.args.exprs)
            self.writeln(f"run {self.current_func}(ret_{self.current_func}, {args2});")
            self.writeln(f"ret_{self.current_func} ? {tmp2};")

            # send back the sum
            self.writeln(f"in_{self.current_func}!({tmp1} + {tmp2});")
            self.writeln("goto end;")
            return

        # fallback: a single function call
        if isinstance(e, c_ast.FuncCall):
            callee = e.name.name
            args   = ','.join(self._expr(a) for a in e.args.exprs)
            self.writeln(f"run {callee}(ret_{callee},{args});")
            self.writeln(f"ret_{callee} ? tmp;")
            self.writeln(f"in_{self.current_func}!tmp;")
            self.writeln("goto end;")
            return

        # fallback: constant or other expression
        val = self._expr(e) if e else '0'
        self.writeln(f"in_{self.current_func}!{val};")
        self.writeln("goto end;")



    def _extract_ptr_base(self, ptr_decl):
        td = ptr_decl.type
        if isinstance(td, c_ast.TypeDecl):
            t = td.type
        # plain typedef’d name: struct node
            if isinstance(t, c_ast.IdentifierType):
                names = t.names
                return names[1] if names[0]=='struct' and len(names)>1 else names[0]
        # inline struct node { … }
            if isinstance(t, c_ast.Struct) and t.name:
                return t.name
        return None

    def _get_sizeof_struct_name(self, node):
        if isinstance(node, c_ast.UnaryOp) and node.op == 'sizeof':
            expr = node.expr

        # sizeof(struct node)
            if isinstance(expr, c_ast.Typename):
                inner = expr.type              # TypeDecl
                if isinstance(inner, c_ast.TypeDecl):
                    idtype = inner.type        # IdentifierType
                    if isinstance(idtype, c_ast.IdentifierType):
                        names = idtype.names
                        return names[1] if names[0] == 'struct' and len(names) > 1 else names[0]
                    if isinstance(idtype,c_ast.Struct) and idtype.name:
                        return idtype.name
        # sizeof(node)  (IdentifierType directly)
            if isinstance(expr, c_ast.IdentifierType):
                names = expr.names
                return names[1] if names[0] == 'struct' and len(names) > 1 else names[0]

        # sizeof(struct node { … })
            if isinstance(expr, c_ast.Struct) and expr.name:
                return expr.name

        return None
    def _expr(self, n):
        if n is None:                     return ''
        if isinstance(n, c_ast.ID):       return n.name
        if isinstance(n, c_ast.Constant): return n.value
        if isinstance(n, c_ast.BinaryOp):
            return f"({self._expr(n.left)} {n.op} {self._expr(n.right)})"
        if isinstance(n, c_ast.UnaryOp):
            return f"({n.op}{self._expr(n.expr)})"
        if isinstance(n, c_ast.ArrayRef):
            return f"{self._expr(n.name)}[{self._expr(n.subscript)}]"
        if isinstance(n, c_ast.StructRef):
            base = self._expr(n.name); fld = n.field.name
            if n.type == '->' and isinstance(n.name, c_ast.ID):
                vt = self.var_types.get(n.name.name)
                if vt and vt[0]=='ptr':
                    return f"{vt[1]}_mem[{base}].{fld}"
            return f"{base}.{fld}"
        return '<expr>'

if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('cfile', help='C source file')
    parser.add_argument('-o','--output', default='output2.pml', help='Output Promela file')
    parser.add_argument('--pool-size', type=int, default=9, help='Memory pool size')
    args = parser.parse_args()

    visitor = CtoPromelaVisitor()
    visitor.pool_size = args.pool_size

    try:
        ast = parse_file(args.cfile, use_cpp=True)
    except Exception as e:
        print(f"Error parsing {args.cfile}: {e}", file=sys.stderr)
        sys.exit(1)

    promela = visitor.visit(ast)
    with open(args.output, 'w') as f:
        f.write(promela)
    print(f"Generated {args.output}")