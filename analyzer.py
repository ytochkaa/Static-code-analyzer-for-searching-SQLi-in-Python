import ast
import sys
import os
from typing import List, Set, Tuple, Optional, Dict
from colorama import init, Fore, Style

init(autoreset=True)

class TaintAnalyzer(ast.NodeVisitor):
    
    def __init__(self):
        self.sources: Set[str] = {
            'request', 'request.GET', 'request.POST', 'request.args', 'request.form',
            'request.json', 'request.data', 'request.headers', 'request.cookies',
            'input', 'sys.argv', 'os.environ', 'environ', 'get', 'cookies.get',
            'headers.get', 'args.get', 'form.get'
        }
        
        self.sinks: Set[str] = {
            'execute', 'executemany', 'executescript', 'query',
            'raw', 'extra', 'text', 'from_statement', 'run'
        }
        
        self.sanitizers: Set[str] = {
            'int', 'float', 'escape_string', 'quote_identifier',
            're.match', 're.fullmatch', 'filter', 'get', 'exclude',
            'sanitize', 'validate', 'escape', 'isalnum', 'isalpha',
            'isdigit', 'isnumeric', 'isdecimal', 'str.encode', 'encode'
        }
        
        self.tainted_variables: Set[str] = set()
        self.sanitized_variables: Set[str] = set()
        self.tainted_functions: Set[str] = set()
        self.variable_origins: Dict[str, str] = {}
        self.current_function: Optional[str] = None
        self.vulnerabilities: List[Tuple[int, str, str, str, str, str]] = []
        self.import_aliases: Dict[str, str] = {}
        self.tree: Optional[ast.AST] = None
        self.source_code: List[str] = []

    def visit_Import(self, node: ast.Import):
        for alias in node.names:
            self.import_aliases[alias.name] = alias.name
        self.generic_visit(node)

    def visit_ImportFrom(self, node: ast.ImportFrom):
        module = node.module or ""
        for alias in node.names:
            self.import_aliases[alias.name] = f"{module}.{alias.name}"
        self.generic_visit(node)

    def visit_FunctionDef(self, node: ast.FunctionDef):
        original_tainted_vars = self.tainted_variables.copy()
        original_sanitized_vars = self.sanitized_variables.copy()
        original_origins = self.variable_origins.copy()
        
        self.tainted_variables = set()
        self.sanitized_variables = set()
        self.current_function = node.name
        
        self.generic_visit(node)
        
        self.tainted_variables = original_tainted_vars
        self.sanitized_variables = original_sanitized_vars
        self.variable_origins = original_origins
        self.current_function = None

    def visit_Return(self, node: ast.Return):
        if node.value and self.current_function:
            if self.is_expression_tainted(node.value):
                self.tainted_functions.add(self.current_function)
        self.generic_visit(node)

    def visit_Assign(self, node: ast.Assign):
        if isinstance(node.value, ast.Call):
            func_chain = self._get_attr_chain(node.value.func)
            func_name = func_chain.split('.')[-1]
            
            if func_name in self.sanitizers:
                for target in node.targets:
                    if isinstance(target, ast.Name):
                        self.sanitized_variables.add(target.id)
                        if target.id in self.tainted_variables:
                            self.tainted_variables.remove(target.id)
                        
                        if node.value.args:
                            arg_source = self._find_ultimate_source(node.value.args[0])
                            if arg_source:
                                self.variable_origins[target.id] = f"Санитизировано из: {arg_source}"
                return
        
        source = self._find_ultimate_source(node.value)
        if source:
            for target in node.targets:
                if isinstance(target, ast.Name):
                    self.variable_origins[target.id] = source
        
        if isinstance(node.value, ast.Name) and node.value.id in self.sanitized_variables:
            for target in node.targets:
                if isinstance(target, ast.Name):
                    self.sanitized_variables.add(target.id)
                    if target.id in self.tainted_variables:
                        self.tainted_variables.remove(target.id)
                    if node.value.id in self.variable_origins:
                        self.variable_origins[target.id] = self.variable_origins[node.value.id]
            return

        if self.is_expression_tainted(node.value):
            for target in node.targets:
                if isinstance(target, ast.Name):
                    self.tainted_variables.add(target.id)
                    if target.id in self.sanitized_variables:
                        self.sanitized_variables.remove(target.id)
        self.generic_visit(node)

    def visit_Call(self, node: ast.Call):
        call_chain = self._get_call_chain(node)
        sink_name = call_chain.split('.')[-1]
        
        if sink_name in self.sinks:
            code_line = self.source_code[node.lineno - 1].strip()
            vuln_type = "ORM Injection" if sink_name in {'raw', 'extra'} else "SQL Injection"
            
            has_additional_args = len(node.args) > 1
            has_named_params = any(
                kw.arg not in (None, 'sql', 'query') 
                for kw in node.keywords
            )
            is_parametrized = has_additional_args or has_named_params
            
            if not is_parametrized and node.args and self.is_expression_tainted(node.args[0]):
                source_info = self._find_source_in_expression(node.args[0])
                problem_info = self._identify_problem_type(node.args[0], call_chain)
                self._report_vulnerability(
                    node, 
                    f"{vuln_type} в {call_chain}",
                    source_info,
                    problem_info,
                    code_line
                )
            
            elif is_parametrized:
                for i, arg in enumerate(node.args[1:], start=1):
                    if self.is_expression_tainted(arg):
                        source_info = self._find_source_in_expression(arg)
                        problem_info = self._identify_problem_type(arg, call_chain)
                        self._report_vulnerability(
                            node, 
                            f"{vuln_type} в параметре {i} {call_chain}",
                            source_info,
                            problem_info,
                            code_line
                        )
                        break
                
                for kw in node.keywords:
                    if kw.arg and kw.arg not in ('sql', 'query') and self.is_expression_tainted(kw.value):
                        source_info = self._find_source_in_expression(kw.value)
                        problem_info = self._identify_problem_type(kw.value, call_chain)
                        self._report_vulnerability(
                            node, 
                            f"{vuln_type} в параметре '{kw.arg}' {call_chain}",
                            source_info,
                            problem_info,
                            code_line
                        )
                        break
                    
        self.generic_visit(node)

    def is_expression_tainted(self, node: ast.AST) -> bool:
        if isinstance(node, ast.Name):
            if node.id in self.sanitized_variables:
                return False
            if node.id in self.tainted_variables:
                return True

        chain_str = self._get_attr_chain(node)
        if any(chain_str.startswith(source) for source in self.sources):
            return True

        if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Mod)):
            return (self.is_expression_tainted(node.left) or 
                    self.is_expression_tainted(node.right))

        if isinstance(node, ast.JoinedStr):
            return any(self.is_expression_tainted(v) for v in node.values)

        if isinstance(node, ast.FormattedValue):
            return self.is_expression_tainted(node.value)

        if isinstance(node, ast.Call):
            full_chain = self._get_attr_chain(node.func)
            func_name = full_chain.split('.')[-1]
            
            if func_name in self.sanitizers:
                return False
                
            if full_chain in self.sources:
                return True
                
            if isinstance(node.func, ast.Attribute) and self.is_expression_tainted(node.func.value):
                return True
                
            func_id = None
            if isinstance(node.func, ast.Name):
                func_id = node.func.id
            elif isinstance(node.func, ast.Attribute):
                func_id = node.func.attr
                
            if func_id and func_id in self.tainted_functions:
                return True
                
            if full_chain.endswith('.format'):
                if self.is_expression_tainted(node.func.value):
                    return True
                for arg in node.args:
                    if self.is_expression_tainted(arg):
                        return True
                for kw in node.keywords:
                    if self.is_expression_tainted(kw.value):
                        return True
                        
            for arg in node.args:
                if self.is_expression_tainted(arg):
                    return True
            for kw in node.keywords:
                if self.is_expression_tainted(kw.value):
                    return True

        if isinstance(node, ast.Subscript):
            return self.is_expression_tainted(node.value)

        if isinstance(node, ast.Attribute):
            return self.is_expression_tainted(node.value)

        return False

    def _find_ultimate_source(self, node: ast.AST) -> Optional[str]:
        if isinstance(node, ast.Name):
            if node.id in self.variable_origins:
                return self.variable_origins[node.id]
            return f"Переменная: {node.id}"

        if isinstance(node, ast.Attribute):
            chain = self._get_attr_chain(node)
            if any(chain.startswith(src) for src in self.sources):
                return chain
            return chain

        if isinstance(node, ast.Call):
            chain = self._get_attr_chain(node.func)
            if chain in self.sources:
                return chain
            if node.args:
                return self._find_ultimate_source(node.args[0])
                
        if isinstance(node, ast.Subscript):
            return self._find_ultimate_source(node.value)
            
        if isinstance(node, ast.BinOp):
            left_src = self._find_ultimate_source(node.left)
            right_src = self._find_ultimate_source(node.right)
            if left_src and right_src:
                return f"{left_src} и {right_src}"
            return left_src or right_src
            
        return None

    def _find_source_in_expression(self, node: ast.AST) -> str:
        if isinstance(node, ast.Name):
            if node.id in self.variable_origins:
                return self.variable_origins[node.id]
            return f"Переменная: {node.id}"

        chain_str = self._get_attr_chain(node)
        if chain_str:
            return chain_str

        if isinstance(node, ast.Call):
            full_chain = self._get_attr_chain(node.func)
            if full_chain in self.sources:
                return full_chain
            if full_chain.split('.')[-1] in self.sources:
                return full_chain

        return "Неизвестный источник"

    def _identify_problem_type(self, node: ast.AST, call_chain: str) -> str:
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
            return "Конкатенация недоверенных строк"
        
        if isinstance(node, (ast.JoinedStr, ast.FormattedValue)):
            return "f-строка/форматирование с недоверенными данными"

        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mod):
            return "Опасное форматирование через оператор %"

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
    
    def _report_vulnerability(
        self, 
        node: ast.AST, 
        title: str, 
        source: str, 
        problem: str,
        code_line: str
    ):
        severity = "Medium"
        
        if "оператор %" in problem or "ORM Injection" in title:
            severity = "High"
        elif "Конкатенация" in problem or ".format()" in problem:
            severity = "High"
        elif "Использование заражённой переменной" in problem:
            severity = "Medium"
        elif "Использование недоверенных данных" in problem:
            severity = "Low"
        
        context = f"Функция: {self.current_function}" if self.current_function else "Глобальная область"
        
        entry = (node.lineno, context, title, source, problem, code_line, severity)
        
        if entry not in self.vulnerabilities:
            self.vulnerabilities.append(entry)

    def get_results(self):
        self.visit(self.tree)
        self.visit(self.tree)
        return sorted(self.vulnerabilities, key=lambda x: x[0])

    def _get_attr_chain(self, node: ast.AST) -> str:
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

def generate_human_report(vulns: list, source_name: str = ""):
    if not vulns:
        print(f"\n{Fore.GREEN}Уязвимостей SQL Injection не обнаружено")
        return
    
    print(f"\n{Fore.MAGENTA}{Style.BRIGHT}Количество уязвимостей в данном файле: {len(vulns)}")
    
    for i, (lineno, context, title, source, problem, code_line, severity) in enumerate(vulns, 1):
        if severity == "High":
            severity_color = Fore.RED
        elif severity == "Medium":
            severity_color = Fore.YELLOW
        else:
            severity_color = Fore.GREEN
        
        print(f"\n{Fore.MAGENTA}Уязвимость {i} (Строка {lineno}):")
        print(f"{severity_color}Уровень опасности: {severity}")
        print(f"Тип: {title}")
        print(f"Источник: {source}")
        print(f"Проблема: {problem}")
        print(f"Контекст: {context}")
        print(f"Код: {code_line}")

def main_menu():
    print("\n" + "="*50)
    print(" СТАТИЧЕСКИЙ АНАЛИЗАТОР SQL INJECTION")
    print("="*50)
    
    print("Меню:")
    print("1. Ввод кода через консоль")
    print("2. Анализ файла")
    print("3. Анализ директории")
    print("4. Выход")
    print("="*50)
        
    choice = input("Выберите режим работы (1-4): ")
        
    if choice == '1':
        print("\n[РЕЖИМ ВВОДА КОДА]")
        print("Введите ваш код. Для завершения введите 'EOF' на новой строке.")
        code_lines = []
        while True:
            line = input()
            if line.strip().upper() == 'EOF':
                break
            code_lines.append(line)
        code = "\n".join(code_lines)
        vulns = analyze_code(code, "консольный ввод")
        generate_human_report(vulns, "консольный ввод")
            
    elif choice == '2':
        print("\n[РЕЖИМ АНАЛИЗА ФАЙЛА]")
        filepath = input("Введите полный путь к файлу: ")
        if os.path.isfile(filepath):
            vulns = analyze_file(filepath)
            generate_human_report(vulns, os.path.basename(filepath))
        else:
            print(f"Ошибка: Файл не найден по пути {filepath}")

    elif choice == '3':
        print("\n[РЕЖИМ АНАЛИЗА ДИРЕКТОРИИ]")
        dirpath = input("Введите путь к директории: ")
        if not os.path.isdir(dirpath):
            print(f"Ошибка: Директория не найдена по пути {dirpath}")
        else:    
            for root, _, files in os.walk(dirpath):
                for file in files:
                    if file.endswith('.py'):
                        full_path = os.path.join(root, file)
                        print(f"\n{Fore.CYAN}Анализ файла: {full_path}")
                        vulns = analyze_file(full_path)
                        generate_human_report(vulns, file)

    elif choice == '4':
        print("Выход из программы.")
        sys.exit(0)
    else:
        print("Ошибка: некорректный выбор. Пожалуйста, введите число от 1 до 4.")    

if __name__ == "__main__":
    if len(sys.argv) > 1:
        filepath = sys.argv[1]
        if os.path.isfile(filepath):
            print(f"{Fore.CYAN}Анализ файла: {filepath}")
            vulns = analyze_file(filepath)
            generate_human_report(vulns, os.path.basename(filepath))
        elif os.path.isdir(filepath):
            for root, _, files in os.walk(filepath):
                for file in files:
                    if file.endswith('.py'):
                        full_path = os.path.join(root, file)
                        print(f"\n{Fore.CYAN}Анализ файла: {full_path}")
                        vulns = analyze_file(full_path)
                        generate_human_report(vulns, file)
        else:
            print(f"Ошибка: Путь не существует: {filepath}")
    else:
        main_menu()