import ast
import sys
import os
from typing import List, Set, Tuple, Optional, Dict, Any

class TaintAnalyzer(ast.NodeVisitor):
    def __init__(self):
        # Источники данных
        self.sources: Set[str] = {
            'request', 'request.GET', 'request.POST', 'request.args', 'request.form',
            'request.json', 'request.data', 'request.headers', 'request.cookies',
            'request.params', 'request.query_string', 'request.values',
            'input', 'sys.argv', 'os.environ', 'environ', 'get', 'cookies.get',
            'headers.get', 'args.get', 'form.get', 'os.getenv', 'json.loads',
            'json.load', 'yaml.load', 'pickle.loads', 'getattr', 'getitem'
        }

        # Синки (SQL)
        self.sinks: Set[str] = {
            'execute', 'executemany', 'executescript', 'query', 'fetchall',
            'fetchone', 'fetchmany', 'commit', 'raw', 'extra', 'text',
            'from_statement', 'run', 'cursor', 'connection'
        }

        # Санитайзеры
        self.sanitizers: Set[str] = {
            'int', 'float', 'str', 'bool', 'escape_string', 'quote_identifier',
            're.match', 're.fullmatch', 're.search', 're.sub', 're.compile',
            'sanitize', 'validate', 'escape', 'isalnum', 'isalpha', 'isdigit',
            'isnumeric', 'isdecimal', 'str.encode', 'encode', 'html.escape',
            'cgi.escape', 'urllib.parse.quote', 'mysql.escape_string',
            'psycopg2.extensions.quote_ident', 'sqlite3.escape_string'
        }

        # Безопасные ORM методы
        self.orm_safe_methods: Set[str] = {
            'filter', 'get', 'all', 'first', 'last', 'exists', 'count',
            'create', 'update', 'delete', 'save', 'using', 'select_related'
        }

        # Трекинг
        self.tainted_variables: Set[str] = set()
        self.sanitized_variables: Set[str] = set()
        self.variable_origins: Dict[str, str] = {}
        self.function_origins: Dict[str, str] = {}
        self.expression_details: Dict[str, str] = {}

        # Контекст
        self.current_function: Optional[str] = None
        self.vulnerabilities: List[Tuple[int, str, str, str, str, str, str]] = []
        self.import_aliases: Dict[str, str] = {}
        self.tree: Optional[ast.AST] = None
        self.source_code: List[str] = []

        # Валидация
        self.validated_vars: Set[str] = set()
        self.allowed_values: Dict[str, Set[str]] = {}

    # --- Импортные алиасы ---
    def visit_Import(self, node: ast.Import):
        for alias in node.names:
            key = alias.asname or alias.name
            self.import_aliases[key] = alias.name
        self.generic_visit(node)

    def visit_ImportFrom(self, node: ast.ImportFrom):
        module = node.module or ""
        for alias in node.names:
            key = alias.asname or alias.name
            self.import_aliases[key] = f"{module}.{alias.name}"
        self.generic_visit(node)

    # --- Функции ---
    def visit_FunctionDef(self, node: ast.FunctionDef):
        # Сохранить окружение
        saved = (
            self.tainted_variables.copy(),
            self.sanitized_variables.copy(),
            self.variable_origins.copy(),
            self.expression_details.copy(),
            self.validated_vars.copy(),
            self.current_function
        )

        # Новый контекст
        self.tainted_variables = set()
        self.sanitized_variables = set()
        self.variable_origins = {}
        self.expression_details = {}
        self.validated_vars = set()
        self.current_function = node.name

        # Аргументы — консервативно tainted
        for arg in node.args.args:
            self.tainted_variables.add(arg.arg)
            self.variable_origins[arg.arg] = f"аргумент функции {node.name}"

        self.generic_visit(node)

        # Восстановление
        (self.tainted_variables,
         self.sanitized_variables,
         self.variable_origins,
         self.expression_details,
         self.validated_vars,
         self.current_function) = saved

    def visit_Return(self, node: ast.Return):
        if node.value and self.current_function:
            origin = self._find_ultimate_source(node.value)
            if origin:
                self.function_origins[self.current_function] = origin
        self.generic_visit(node)

    # --- Присваивания ---
    def visit_Assign(self, node: ast.Assign):
        # 1) Санитизация через вызовы (int(...), html.escape(...))
        if isinstance(node.value, ast.Call):
            func_chain = self._get_attr_chain(node.value.func)
            if any(s in func_chain for s in self.sanitizers):
                for target in node.targets:
                    if isinstance(target, ast.Name):
                        self.sanitized_variables.add(target.id)
                        self.tainted_variables.discard(target.id)
                        if node.value.args:
                            arg_src = self._find_ultimate_source(node.value.args[0])
                            self.variable_origins[target.id] = f"Санитизировано из: {arg_src}"
                self.generic_visit(node)
                return

        # 2) .format() — если аргументы tainted, то результат tainted
        if isinstance(node.value, ast.Call):
            if isinstance(node.value.func, ast.Attribute) and node.value.func.attr == 'format':
                # если любой аргумент format() заражён — помечаем целевую переменную
                for fmt_arg in node.value.args:
                    if self.is_expression_tainted(fmt_arg):
                        for target in node.targets:
                            if isinstance(target, ast.Name):
                                self.tainted_variables.add(target.id)
                                self.variable_origins[target.id] = f"Форматирование .format()"
                                self.expression_details[target.id] = self._get_expression_details(node.value)
                        break

        # 3) f-строки (JoinedStr) и бинарные оп. с конкатенацией/%
        if isinstance(node.value, ast.JoinedStr):
            # если в f-string есть tainted фрагменты — результат tainted
            for v in node.value.values:
                if isinstance(v, ast.FormattedValue) and self.is_expression_tainted(v.value):
                    for target in node.targets:
                        if isinstance(target, ast.Name):
                            self.tainted_variables.add(target.id)
                            self.variable_origins[target.id] = self._find_ultimate_source(node.value)
                            self.expression_details[target.id] = self._get_expression_details(node.value)
                    break

        if isinstance(node.value, ast.BinOp) and isinstance(node.value.op, (ast.Add, ast.Mod)):
            if self.is_expression_tainted(node.value):
                for target in node.targets:
                    if isinstance(target, ast.Name):
                        self.tainted_variables.add(target.id)
                        self.variable_origins[target.id] = self._find_ultimate_source(node.value)
                        self.expression_details[target.id] = self._get_expression_details(node.value)

        # 4) Вызов локальной функции с известным возвратом
        if isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name):
            fname = node.value.func.id
            if fname in self.function_origins:
                src = self.function_origins[fname]
                for target in node.targets:
                    if isinstance(target, ast.Name):
                        self.variable_origins[target.id] = f"Возврат функции {fname}: {src}"
                        if any(s in src.lower() for s in ['request', 'input', 'argv', 'environ', 'cookies']):
                            self.tainted_variables.add(target.id)

        # 5) Общая логика: определение источника и taint на основе RHS
        source = self._find_ultimate_source(node.value)
        expr = self._get_expression_details(node.value)
        if source:
            for target in node.targets:
                if isinstance(target, ast.Name):
                    # не перезаписываем более точную информацию о санитизации
                    if target.id not in self.sanitized_variables:
                        self.variable_origins[target.id] = source
                        self.expression_details[target.id] = expr
                        if any(s in source.lower() for s in ['request', 'input', 'argv', 'environ', 'cookies', 'get', 'post']):
                            self.tainted_variables.add(target.id)

        # 6) Если RHS сам по себе tainted (рекурсивно), помечаем target
        if self.is_expression_tainted(node.value):
            for target in node.targets:
                if isinstance(target, ast.Name):
                    self.tainted_variables.add(target.id)

        self.generic_visit(node)

    # --- Валидация (If) ---
    def _is_validation_call(self, node: ast.Call) -> bool:
        if isinstance(node.func, ast.Attribute) and node.func.attr in {'__contains__', 'issubset'}:
            return True
        if isinstance(node.func, ast.Attribute) and node.func.attr in {'isdigit', 'isnumeric', 'isdecimal', 'isalpha', 'isalnum'}:
            return True
        return False

    def visit_If(self, node: ast.If):
        if isinstance(node.test, ast.Compare):
            left = node.test.left
            if isinstance(left, ast.Name) and left.id in self.tainted_variables:
                if (len(node.test.ops) > 0 and isinstance(node.test.ops[0], ast.In)
                    and isinstance(node.test.comparators[0], ast.Set)):
                    allowed_values = {elt.value for elt in node.test.comparators[0].elts if isinstance(elt, ast.Constant)}
                    self.allowed_values[left.id] = allowed_values
                    self.validated_vars.add(left.id)
                elif (len(node.test.ops) > 0 and isinstance(node.test.ops[0], (ast.Eq, ast.NotEq))
                      and isinstance(node.test.comparators[0], ast.Constant)):
                    self.validated_vars.add(left.id)
        self.generic_visit(node)

    # --- Параметризация ---
    def _is_parametrized_query(self, node: ast.Call, call_chain: str) -> bool:
        # explicit params: execute(sql, params)
        if len(node.args) > 1:
            return True
        # args[1] — tuple/list/dict
        if len(node.args) == 2 and isinstance(node.args[1], (ast.Tuple, ast.List, ast.Dict, ast.Set)):
            return True
        if any(kw.arg in ('params', 'parameters') for kw in node.keywords):
            return True
        if any(method in call_chain for method in self.orm_safe_methods):
            return True
        return False

    # --- Вызовы (sinks и источники) ---
    def visit_Call(self, node: ast.Call):
        call_chain = self._get_call_chain(node)
        sink_name = call_chain.split('.')[-1] if call_chain else ""

        # Если sink — потенциально SQL
        if sink_name in self.sinks:
            code_line = ""
            if self.source_code and 1 <= getattr(node, 'lineno', 0) <= len(self.source_code):
                code_line = self.source_code[node.lineno - 1].rstrip()
            vuln_type = "ORM Injection" if sink_name in {'raw', 'extra'} else "SQL Injection"
            is_param = self._is_parametrized_query(node, call_chain)

            # ИГНОРИРОВАТЬ безопасные параметризованные запросы
            if is_param and len(node.args) > 1:
                # Проверяем только SQL-шаблон (первый аргумент), но игнорируем параметры
                sql_arg = node.args[0]
                # Если SQL-шаблон заражен - это уязвимость
                if self.is_expression_tainted(sql_arg):
                    src_info = self._find_source_in_expression(sql_arg)
                    problem = "SQL-шаблон сформирован из недоверенных данных"
                    self._report_vulnerability(node, f"{vuln_type} в {call_chain}", src_info, problem, code_line)
            # Если не параметризован — проверяем аргументы (обычно первый аргумент — SQL)
            elif not is_param and node.args:
                sql_arg = node.args[0]
                # Если SQL — выражение (f-string, concat, format), и содержит tainted => vuln
                if self.is_expression_tainted(sql_arg):
                    src_info = self._find_source_in_expression(sql_arg)
                    problem = self._identify_problem_type(sql_arg, call_chain)
                    self._report_vulnerability(node, f"{vuln_type} в {call_chain}", src_info, problem, code_line)
                # Если SQL — переменная (Name), но та переменная хранит tainted-источник — тоже vuln
                elif isinstance(sql_arg, ast.Name) and sql_arg.id in self.variable_origins:
                    origin = self.variable_origins[sql_arg.id]
                    if any(s in origin.lower() for s in ['request', 'input', 'argv', 'environ', 'cookies']):
                        src_info = f"{sql_arg.id} (данные из: {origin})"
                        problem = "Использование переменной с недоверенным происхождением в SQL"
                        self._report_vulnerability(node, f"{vuln_type} в {call_chain}", src_info, problem, code_line)

        # Источники: request.GET.get(...), request.cookies.get(...)
        if isinstance(node.func, ast.Attribute):
            chain = self._get_attr_chain(node.func)
            for src in self.sources:
                if chain == src or chain.startswith(src):
                    for arg in node.args:
                        if isinstance(arg, ast.Name):
                            self.tainted_variables.add(arg.id)
                            self.variable_origins[arg.id] = chain
                    break

        self.generic_visit(node)

    # --- Проверка, содержит ли выражение tainted данные ---
    def is_expression_tainted(self, node: ast.AST) -> bool:
        if node is None:
            return False

        if isinstance(node, ast.Name):
            if node.id in self.sanitized_variables:
                return False
            if node.id in self.validated_vars:
                return False
            return node.id in self.tainted_variables

        if isinstance(node, ast.Attribute):
            chain = self._get_attr_chain(node)
            for src in self.sources:
                if chain == src or chain.startswith(src):
                    return True
            return self.is_expression_tainted(node.value)

        if isinstance(node, ast.Subscript):
            if self.is_expression_tainted(node.value):
                return True
            slice_node = getattr(node, 'slice', None)
            if slice_node and self.is_expression_tainted(slice_node):
                return True
            return False

        if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Mod)):
            return self.is_expression_tainted(node.left) or self.is_expression_tainted(node.right)

        if isinstance(node, ast.JoinedStr):
            for v in node.values:
                if isinstance(v, ast.FormattedValue) and self.is_expression_tainted(v.value):
                    return True
            return False

        if isinstance(node, ast.FormattedValue):
            return self.is_expression_tainted(node.value)

        if isinstance(node, ast.Call):
            func_chain = self._get_attr_chain(node.func)
            # санитайзеры очищают
            if any(s in func_chain for s in self.sanitizers):
                return False
            # вызов источника
            for src in self.sources:
                if func_chain == src or func_chain.startswith(src):
                    return True
            # вызов локальной функции с известным возвратом
            if isinstance(node.func, ast.Name):
                fname = node.func.id
                if fname in self.function_origins:
                    origin = self.function_origins[fname]
                    if any(s in origin.lower() for s in ['request', 'input', 'argv', 'environ', 'cookies']):
                        return True
            # рекурсивно смотрим по аргументам
            for arg in node.args:
                if self.is_expression_tainted(arg):
                    return True
            for kw in node.keywords:
                if self.is_expression_tainted(kw.value):
                    return True
            return False

        if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
            return any(self.is_expression_tainted(elt) for elt in node.elts)

        if isinstance(node, ast.Constant):
            return False

        return False

    # --- Представление выражений и источников ---
    def _get_expression_details(self, node: ast.AST) -> str:
        if node is None:
            return ""
        if isinstance(node, ast.Constant):
            return repr(node.value)
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Attribute):
            return f"{self._get_expression_details(node.value)}.{node.attr}"
        if isinstance(node, ast.Call):
            func = self._get_expression_details(node.func)
            args = [self._get_expression_details(a) for a in node.args]
            return f"{func}({', '.join(args)})"
        if isinstance(node, ast.JoinedStr):
            parts = []
            for v in node.values:
                if isinstance(v, ast.Constant):
                    parts.append(str(v.value))
                elif isinstance(v, ast.FormattedValue):
                    parts.append("{" + self._get_expression_details(v.value) + "}")
            return "f'" + "".join(parts) + "'"
        if isinstance(node, ast.BinOp):
            left = self._get_expression_details(node.left)
            right = self._get_expression_details(node.right)
            op = self._get_op_symbol(node.op)
            return f"({left} {op} {right})"
        if isinstance(node, ast.Subscript):
            return f"{self._get_expression_details(node.value)}[...]"
        return "complex_expression"

    def _get_op_symbol(self, op: ast.operator) -> str:
        if isinstance(op, ast.Add):
            return "+"
        if isinstance(op, ast.Mod):
            return "%"
        if isinstance(op, ast.Mult):
            return "*"
        if isinstance(op, ast.Sub):
            return "-"
        return "op"

    def _find_ultimate_source(self, node: ast.AST) -> str:
        if node is None:
            return ""
        if isinstance(node, ast.Name):
            if node.id in self.variable_origins:
                return self.variable_origins[node.id]
            return f"Переменная: {node.id}"
        if isinstance(node, ast.Attribute):
            return self._get_attr_chain(node)
        if isinstance(node, ast.Call):
            chain = self._get_attr_chain(node.func)
            for src in self.sources:
                if chain == src or chain.startswith(src):
                    args_src = []
                    for arg in node.args:
                        if isinstance(arg, (ast.Constant, ast.Name)):
                            args_src.append(self._find_ultimate_source(arg))
                    return f"{chain}({', '.join(args_src)})"
            if isinstance(node.func, ast.Name):
                fname = node.func.id
                if fname in self.function_origins:
                    return f"Возврат функции {fname}: {self.function_origins[fname]}"
            return chain
        if isinstance(node, ast.JoinedStr):
            parts = []
            for v in node.values:
                if isinstance(v, ast.FormattedValue):
                    parts.append("{" + self._find_ultimate_source(v.value) + "}")
                elif isinstance(v, ast.Constant):
                    parts.append(str(v.value))
            return "f'" + "".join(parts) + "'"
        if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Mod)):
            left = self._find_ultimate_source(node.left)
            right = self._find_ultimate_source(node.right)
            return f"{left} {self._get_op_symbol(node.op)} {right}"
        if isinstance(node, ast.Subscript):
            base = self._find_ultimate_source(node.value)
            return f"{base}[...]"
        if isinstance(node, ast.Constant):
            return f"Константа: {node.value}"
        return "Сложное выражение"

    def _find_source_in_expression(self, node: ast.AST) -> str:
        if isinstance(node, ast.Name):
            expr = self.expression_details.get(node.id, node.id)
            if node.id in self.variable_origins:
                return f"{expr} (данные из: {self.variable_origins[node.id]})"
            return f"Переменная: {node.id}"
        source = self._find_ultimate_source(node)
        expr = self._get_expression_details(node)
        return f"{expr} (данные из: {source})"

    # --- Проблема/тип ---
    def _identify_problem_type(self, node: ast.AST, call_chain: str) -> str:
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
            return "Конкатенация недоверенных строк"
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mod):
            return "Опасное форматирование через оператор %"
        if isinstance(node, (ast.JoinedStr, ast.FormattedValue)):
            return "f-строка с недоверенными данными"
        if isinstance(node, ast.Call):
            func_chain = self._get_attr_chain(node.func)
            if func_chain.endswith('.format'):
                return "Небезопасное использование .format()"
            if any(func_chain.startswith(src) for src in self.sources):
                return "Прямой вызов источника данных"
            if call_chain.endswith(('.raw', '.extra')):
                return "Прямая подстановка пользовательского ввода"
        if isinstance(node, ast.Name) and node.id in self.tainted_variables:
            return "Использование заражённой переменной"
        if isinstance(node, ast.Attribute):
            return f"Использование недоверенного атрибута: {node.attr}"
        return "Использование недоверенных данных"

    # --- Регистрируем уязвимость (и контекст вокруг строки) ---
    def _report_vulnerability(self, node: ast.AST, title: str, source: str, problem: str, code_line: str):
        severity = "Low"
        critical = ["%", "ORM Injection", "Конкатенация", ".format(", "f-строка", "raw", "extra", "text(", "from_statement"]
        medium = ["Использование заражённой переменной", "Прямой вызов", "подстановка"]
        if any(p in problem or p in title for p in critical):
            severity = "High"
        elif any(p in problem for p in medium):
            severity = "Medium"
        context = f"Функция: {self.current_function}" if self.current_function else "Глобальная область"
        entry = (node.lineno, context, title, source, problem, code_line, severity)
        if entry not in self.vulnerabilities:
            self.vulnerabilities.append(entry)

    # --- Запуск ---
    def get_results(self):
        if self.tree:
            self.visit(self.tree)
        return sorted(self.vulnerabilities, key=lambda x: x[0])

    # --- Цепочки атрибутов ---
    def _get_attr_chain(self, node: ast.AST) -> str:
        if node is None:
            return ""
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Attribute):
            base = self._get_attr_chain(node.value)
            return f"{base}.{node.attr}" if base else node.attr
        if isinstance(node, ast.Call):
            return self._get_attr_chain(node.func)
        if isinstance(node, ast.Subscript):
            return self._get_attr_chain(node.value)
        return ""

    def _get_call_chain(self, node: ast.Call) -> str:
        return self._get_attr_chain(node.func)


# ---------------- API функции ----------------
def analyze_code(code: str, filename: str = "input"):
    try:
        tree = ast.parse(code, filename=filename)
        analyzer = TaintAnalyzer()
        analyzer.tree = tree
        analyzer.source_code = code.splitlines()
        return analyzer.get_results()
    except SyntaxError as e:
        print(f"Ошибка синтаксиса в файле {filename}: {e}")
        return []
    except Exception as e:
        print(f"Неизвестная ошибка при анализе кода: {e}")
        return []

def analyze_file(filename: str):
    try:
        with open(filename, 'r', encoding='utf-8') as f:
            code = f.read()
        return analyze_code(code, filename)
    except FileNotFoundError:
        print(f"Файл не найден: {filename}")
        return []
    except Exception as e:
        print(f"Ошибка при анализе файла {filename}: {e}")
        return []

# ---------------- Отчёт (включая контекст строк) ----------------
def generate_report(vulns: list, source_name: str = ""):
    COLORS = {
        'RED': '\033[91m',
        'GREEN': '\033[92m',
        'YELLOW': '\033[93m',
        'PURPLE': '\033[95m',
        'BOLD_PURPLE': '\033[1;95m',
        'BOLD_WHITE': '\033[1;97m',
        'WHITE': '\033[97m',
        'BOLD': '\033[1m',
        'END': '\033[0m'
    }
    def color_text(text, color):
        return f"{COLORS.get(color, '')}{text}{COLORS['END']}"

    if not vulns:
        print(f"\n{color_text('РЕЗУЛЬТАТ АНАЛИЗА: УЯЗВИМОСТЕЙ НЕ ОБНАРУЖЕНО', 'BOLD')}")
        return

    print(f"\n{color_text('=' * 150, 'PURPLE')}")
    print(f"{color_text('ОТЧЕТ ОБ АНАЛИЗЕ БЕЗОПАСНОСТИ', 'BOLD_WHITE')}")
    print(f"{color_text('=' * 150, 'PURPLE')}")
    print(f"{color_text('ОБНАРУЖЕНЫ КРИТИЧЕСКИЕ УЯЗВИМОСТИ SQL INJECTION', 'RED')}")
    print(f"{color_text('АНАЛИЗИРУЕМЫЙ ОБЪЕКТ:', 'BOLD_WHITE')} {source_name}")
    print(f"{color_text('ВСЕГО УЯЗВИМОСТЕЙ:', 'BOLD_WHITE')} {color_text(str(len(vulns)), 'RED')}")
    high_count = sum(1 for v in vulns if v[6] == 'High')
    medium_count = sum(1 for v in vulns if v[6] == 'Medium')
    low_count = sum(1 for v in vulns if v[6] == 'Low')
    print(f"{color_text('КРИТИЧЕСКИЕ (High):', 'BOLD_WHITE')} {color_text(str(high_count), 'RED')}")
    print(f"{color_text('СРЕДНИЕ (Medium):', 'BOLD_WHITE')} {color_text(str(medium_count), 'YELLOW')}")
    print(f"{color_text('НИЗКИЕ (Low):', 'BOLD_WHITE')} {color_text(str(low_count), 'GREEN')}")
    print(f"{color_text('ДАТА АНАЛИЗА:', 'BOLD_WHITE')} {__import__('datetime').datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"{color_text('=' * 150, 'PURPLE')}")
    print(f"{color_text('ДЕТАЛИЗИРОВАННЫЙ ОТЧЕТ:', 'BOLD_WHITE')}")
    print(f"{color_text('=' * 150, 'PURPLE')}")

    for i, (lineno, context, title, source, problem, code_line, severity) in enumerate(vulns, 1):
        if severity == "High":
            sev_color = 'RED'
            sev_disp = "High"
        elif severity == "Medium":
            sev_color = 'YELLOW'
            sev_disp = "Medium"
        else:
            sev_color = 'GREEN'
            sev_disp = "Low"
        print(f"{color_text(f'Уязвимость {i} (строка {lineno}):', 'BOLD')}")
        print(f"{color_text('Уровень опасности:', 'PURPLE')} {color_text(sev_disp, sev_color)}")
        print(f"{color_text('Тип:', 'PURPLE')} {title}")
        print(f"{color_text('Проблема:', 'PURPLE')} {problem}")
        print(f"{color_text('Контекст выполнения:', 'PURPLE')} {context}")
        print(f"{color_text('Источник недоверенных данных:', 'PURPLE')}")
        for line in source.split('\n'):
            print(f"    {line}")
        # Контекст кода ±2 строки
        print(f"{color_text('Уязвимый код:', 'PURPLE')}")
        try:
            if os.path.isfile(source_name):
                with open(source_name, 'r', encoding='utf-8') as f:
                    lines = f.read().splitlines()
                start = max(0, lineno-3)
                end = min(len(lines), lineno+2)
                for idx in range(start, end):
                    prefix = ">>" if (idx+1) == lineno else "  "
                    print(f" {color_text('{prefix}', 'RED')} {idx+1:4d}: {lines[idx]}")
            else:
                if code_line:
                    print(f"    {code_line}")
        except Exception:
            if code_line:
                print(f"    {code_line}")
        print(f"{color_text('-' * 150, 'WHITE')}")

    print(f"{color_text('=' * 150, 'PURPLE')}")
    print(f"{color_text('РЕКОМЕНДАЦИИ ПО УСТРАНЕНИЮ:', 'BOLD_WHITE')}")
    print(f"{color_text('1.', 'PURPLE')} Замените конкатенацию строк на параметризованные запросы")
    print(f"{color_text('2.', 'PURPLE')} Используйте встроенные механизмы ORM для безопасных запросов")
    print(f"{color_text('3.', 'PURPLE')} Валидируйте и санитизируйте все пользовательские входные данные")
    print(f"{color_text('4.', 'PURPLE')} Применяйте prepared statements для всех SQL операций")
    print(f"{color_text('5.', 'PURPLE')} Ограничьте привилегии учетной записи базы данных")
    print(f"{color_text('6.', 'PURPLE')} Реализуйте механизмы логирования и мониторинга запросов")
    print(f"\n{color_text('ПРИОРИТЕТЫ ИСПРАВЛЕНИЯ:', 'BOLD_WHITE')}")
    print(f"{color_text('-' * 150, 'PURPLE')}")
    print(f"{color_text('•', 'RED')} Критические угрозы (High) - требуют немедленного исправления")
    print(f"{color_text('•', 'YELLOW')} Средние угрозы (Medium) - исправить в ближайшем релизе")
    print(f"{color_text('•', 'GREEN')} Потенциальные риски (Low) - исправить при следующем рефакторинге")
    print(f"\n{color_text('=' * 150, 'PURPLE')}")
    print(f"{color_text('АНАЛИЗ ЗАВЕРШЕН', 'BOLD_WHITE')}")
    print(f"{color_text('=' * 150, 'PURPLE')}\n")


# --- Главное меню ---
def main_menu():
    COLORS = {
        'PURPLE': '\033[95m',
        'RED': '\033[91m',
        'BOLD_WHITE': '\033[1;97m',
        'BOLD': '\033[1m',
        'END': '\033[0m'
    }
    def color_text(text, color):
        return f"{COLORS.get(color, '')}{text}{COLORS['END']}"
    while True:
        print(f"\n{color_text('=' * 150, 'PURPLE')}")
        print(f"{color_text('СТАТИЧЕСКИЙ АНАЛИЗАТОР SQL INJECTION', 'BOLD_WHITE')}")
        print(f"{color_text('=' * 150, 'PURPLE')}")
        print(f"{color_text('ДОСТУПНЫЕ РЕЖИМЫ РАБОТЫ:', 'BOLD_WHITE')}")
        print(f"{color_text('1.', 'PURPLE')} Ввод исходного кода для анализа")
        print(f"{color_text('2.', 'PURPLE')} Анализ файла с исходным кодом")
        print(f"{color_text('3.', 'PURPLE')} Рекурсивный анализ директории")
        print(f"{color_text('4.', 'PURPLE')} Завершение работы системы")
        print(f"{color_text('-' * 150, 'PURPLE')}")
        choice = input(f"{color_text('Введите номер режима (1-4):', 'BOLD_WHITE')} ")
        if choice == '1':
            print(f"{color_text('РЕЖИМ АНАЛИЗА ИСХОДНОГО КОДА', 'BOLD_WHITE')}")
            print(f"{color_text('Введите код для анализа. Для завершения введите EOF на новой строке.', 'PURPLE')}")
            code_lines = []
            while True:
                try:
                    line = input()
                    if line.strip().upper() == 'EOF':
                        break
                    code_lines.append(line)
                except EOFError:
                    break
            code = "\n".join(code_lines)
            vulns = analyze_code(code, "прямой ввод кода")
            generate_report(vulns, "непосредственный ввод кода")
        elif choice == '2':
            print(f"{color_text('РЕЖИМ АНАЛИЗА ФАЙЛА', 'BOLD_WHITE')}")
            filepath = input(f"{color_text('Введите путь к файлу для анализа:', 'BOLD_WHITE')} ")
            if os.path.isfile(filepath):
                vulns = analyze_file(filepath)
                generate_report(vulns, os.path.abspath(filepath))
            else:
                print(f"{color_text('ОШИБКА: Указанный файл не существует', 'RED')}")
        elif choice == '3':
            print(f"{color_text('РЕЖИМ АНАЛИЗА ДИРЕКТОРИИ', 'BOLD_WHITE')}")
            dirpath = input(f"{color_text('Введите путь к директории для анализа:', 'BOLD_WHITE')} ")
            if not os.path.isdir(dirpath):
                print(f"{color_text('ОШИБКА: Указанная директория не существует', 'RED')}")
            else:
                for root, _, files in os.walk(dirpath):
                    for file in files:
                        if file.endswith('.py'):
                            full_path = os.path.join(root, file)
                            print(f"\n{color_text('Анализ файла:', 'BOLD_WHITE')} {full_path}")
                            vulns = analyze_file(full_path)
                            generate_report(vulns, os.path.abspath(full_path))
        elif choice == '4':
            print(f"{color_text('Завершение работы системы анализа безопасности.', 'BOLD_WHITE')}")
            sys.exit(0)
        else:
            print(f"{color_text('ОШИБКА: Некорректный выбор. Введите число от 1 до 4.', 'RED')}")

if __name__ == "__main__":
    if len(sys.argv) > 1:
        filepath = sys.argv[1]
        if os.path.isfile(filepath):
            print(f">>> Анализ файла: {filepath}")
            vulns = analyze_file(filepath)
            generate_report(vulns, os.path.basename(filepath))
        elif os.path.isdir(filepath):
            for root, _, files in os.walk(filepath):
                for file in files:
                    if file.endswith('.py'):
                        full_path = os.path.join(root, file)
                        print(f"\n>>> Анализ файла: {full_path}")
                        vulns = analyze_file(full_path)
                        generate_report(vulns, file)
        else:
            print(f"Ошибка: Путь не существует: {filepath}")
    else:
        main_menu()
