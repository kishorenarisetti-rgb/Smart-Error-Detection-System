#!/usr/bin/env python3
"""=============================================================================
SMART ERROR DETECTION SYSTEM (SEDS) 2.0 - ALL-IN-ONE STANDALONE EDITION
Tagline: Detect. Fix. Run. Automatically.

This single file contains the complete SEDS application:
1. Error Detection Engine (Python AST, Tokenize, Traceback Parser)
   - Detects all 12 core errors: SyntaxError, NameError, TypeError, IndexError,
     ZeroDivisionError, IndentationError, TabError, KeyError, ValueError,
     AttributeError, ImportError, ModuleNotFoundError.
   - Detects missing brackets (), [], {}, unclosed quotes, missing colons,
     undefined variables, argument mismatches, and logical warnings.
2. 7-Point AI Error Explainer (What, Where, Why, Cause, Affected, How to Fix, Corrected Code)
   - Full offline heuristic explanation engine + optional OpenAI & Gemini integration.
3. Intelligent Auto-Fixer with AST syntax validation, Diff generator, and Undo stack.
4. Isolated Code Runner with scrubbed environment (no secret leakage) and watchdog timeout.
5. Multi-File Project Scanner (read-only AST scanner with pass/fail reports).
6. SQLite Database persistence for sessions, error history, and analytics.
7. Embedded Modern VS Code Dark Web UI (HTML, CSS, JS) served via built-in Flask server.
8. Optional Native Tkinter GUI Mode (run with --tkinter).

Usage:
    python SEDS.py             # Launches modern VS Code Dark Web IDE at http://127.0.0.1:5000
    python SEDS.py --tkinter   # Launches native Tkinter desktop interface
    python SEDS.py --no-browser# Starts web server without auto-opening browser
============================================================================="""

from __future__ import annotations

import ast
import builtins
import difflib
import io
import json
import os
import re
import shutil
import sqlite3
import subprocess
import sys
import tempfile
import time
import token
import tokenize
import webbrowser
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

from flask import Flask, Response, jsonify, request
from flask_cors import CORS

# Try to load .env if python-dotenv is installed
try:
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:
    pass

# =============================================================================
# 1. ERROR DETECTION ENGINE (AST, TOKENIZE & TRACEBACK)
# =============================================================================

@dataclass
class DetectedError:
    error_type: str
    message: str
    line: int
    column: int = 1
    end_line: Optional[int] = None
    end_column: Optional[int] = None
    source_snippet: str = ""
    category: str = "syntax"  # 'token', 'syntax', 'ast_static', 'runtime', 'logical'
    severity: str = "error"   # 'error', 'warning', 'info'
    details: Optional[Dict[str, Any]] = None

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


class TokenAnalyzer:
    """Performs token-level inspection for unclosed brackets, quotes, and tabs."""

    BRACKET_PAIRS = {"(": ")", "[": "]", "{": "}"}
    REVERSE_BRACKET_PAIRS = {")": "(", "]": "[", "}": "{"}

    @classmethod
    def analyze(cls, code: str) -> List[DetectedError]:
        errors: List[DetectedError] = []
        lines = code.splitlines()

        # Check for mixed tabs and spaces first
        for idx, line in enumerate(lines, start=1):
            leading = line[: len(line) - len(line.lstrip())]
            if "\t" in leading and " " in leading:
                errors.append(
                    DetectedError(
                        error_type="TabError",
                        message="Inconsistent indentation: line mixes tabs and spaces.",
                        line=idx,
                        column=1,
                        source_snippet=line,
                        category="token",
                        severity="error",
                        details={"issue": "mixed_tabs_spaces"},
                    )
                )

        bracket_stack: List[Tuple[str, int, int]] = []  # (char, line, col)
        stream = io.StringIO(code)

        try:
            for tok in tokenize.generate_tokens(stream.readline):
                tok_type = tok.type
                tok_str = tok.string
                srow, scol = tok.start

                if tok_type == token.OP:
                    if tok_str in cls.BRACKET_PAIRS:
                        bracket_stack.append((tok_str, srow, scol + 1))
                    elif tok_str in cls.REVERSE_BRACKET_PAIRS:
                        expected_open = cls.REVERSE_BRACKET_PAIRS[tok_str]
                        if not bracket_stack:
                            line_content = lines[srow - 1] if srow <= len(lines) else ""
                            errors.append(
                                DetectedError(
                                    error_type="SyntaxError",
                                    message=f"Unmatched closing bracket '{tok_str}' with no matching opening '{expected_open}'.",
                                    line=srow,
                                    column=scol + 1,
                                    source_snippet=line_content,
                                    category="token",
                                    severity="error",
                                    details={"issue": "unmatched_closing", "bracket": tok_str},
                                )
                            )
                        else:
                            last_open, last_row, _ = bracket_stack.pop()
                            if last_open != expected_open:
                                line_content = lines[srow - 1] if srow <= len(lines) else ""
                                errors.append(
                                    DetectedError(
                                        error_type="SyntaxError",
                                        message=f"Mismatched bracket: expected '{cls.BRACKET_PAIRS[last_open]}' to close '{last_open}' from line {last_row}, but found '{tok_str}'.",
                                        line=srow,
                                        column=scol + 1,
                                        source_snippet=line_content,
                                        category="token",
                                        severity="error",
                                        details={
                                            "issue": "mismatched_brackets",
                                            "opened": last_open,
                                            "opened_line": last_row,
                                            "closed": tok_str,
                                        },
                                    )
                                )

            # If unclosed brackets remain in stack
            for unclosed, urow, ucol in bracket_stack:
                closing = cls.BRACKET_PAIRS[unclosed]
                bracket_name = {
                    "(": "parenthesis ')'",
                    "[": "square bracket ']'",
                    "{": "curly brace '}'",
                }.get(unclosed, f"'{closing}'")
                line_content = lines[urow - 1] if urow <= len(lines) else ""
                errors.append(
                    DetectedError(
                        error_type="SyntaxError",
                        message=f"Missing closing {bracket_name} opened at line {urow}, column {ucol}.",
                        line=urow,
                        column=ucol,
                        source_snippet=line_content,
                        category="token",
                        severity="error",
                        details={
                            "issue": "unclosed_bracket",
                            "bracket": unclosed,
                            "expected": closing,
                            "open_line": urow,
                            "open_col": ucol,
                        },
                    )
                )

        except tokenize.TokenError as exc:
            msg, (erow, ecol) = exc.args
            line_content = lines[erow - 1] if 1 <= erow <= len(lines) else ""
            if bracket_stack and "multi-line statement" in msg:
                for unclosed, urow, ucol in bracket_stack:
                    closing = cls.BRACKET_PAIRS[unclosed]
                    bracket_name = {
                        "(": "parenthesis ')'",
                        "[": "square bracket ']'",
                        "{": "curly brace '}'",
                    }.get(unclosed, f"'{closing}'")
                    err_snippet = lines[urow - 1] if urow <= len(lines) else ""
                    errors.append(
                        DetectedError(
                            error_type="SyntaxError",
                            message=f"Missing closing {bracket_name} opened at line {urow}, column {ucol}.",
                            line=urow,
                            column=ucol,
                            source_snippet=err_snippet,
                            category="token",
                            severity="error",
                            details={
                                "issue": "unclosed_bracket",
                                "bracket": unclosed,
                                "expected": closing,
                                "open_line": urow,
                                "open_col": ucol,
                            },
                        )
                    )
            elif (
                "unterminated string literal" in msg.lower()
                or "unterminated triple-quoted string" in msg.lower()
                or "eof in multi-line string" in msg.lower()
                or "eol while scanning string literal" in msg.lower()
            ):
                det_line = erow
                match_det = re.search(r"detected at line (\d+)", msg)
                if match_det:
                    det_line = int(match_det.group(1))

                target_line = lines[det_line - 1] if 1 <= det_line <= len(lines) else line_content

                quote_char = None
                open_col = ecol or 1
                i = 0
                while i < len(target_line):
                    ch = target_line[i]
                    if ch == "\\" and quote_char:
                        i += 2
                        continue
                    if ch in ('"', "'"):
                        if i + 2 < len(target_line) and target_line[i : i + 3] == ch * 3:
                            q = ch * 3
                            if quote_char == q:
                                quote_char = None
                            elif quote_char is None:
                                quote_char = q
                                open_col = i + 1
                            i += 3
                            continue
                        if quote_char == ch:
                            quote_char = None
                        elif quote_char is None:
                            quote_char = ch
                            open_col = i + 1
                    i += 1

                q_name = (
                    "double quote ('\"')"
                    if quote_char in ('"', '"""')
                    else ("single quote ('\\'')" if quote_char in ("'", "'''") else "quotation mark")
                )

                errors.append(
                    DetectedError(
                        error_type="SyntaxError",
                        message=f"Unterminated string literal: string opened with {q_name} at line {det_line}, column {open_col} was not closed.",
                        line=det_line,
                        column=open_col,
                        source_snippet=target_line,
                        category="token",
                        severity="error",
                        details={
                            "issue": "unclosed_string",
                            "quote": quote_char or ('"' if '"' in target_line else "'"),
                            "open_line": det_line,
                            "open_col": open_col,
                            "raw_message": msg,
                        },
                    )
                )
            elif "EOF in multi-line statement" in msg:
                errors.append(
                    DetectedError(
                        error_type="SyntaxError",
                        message="Unclosed bracket, parenthesis, or statement at end of code.",
                        line=erow,
                        column=ecol or 1,
                        source_snippet=line_content,
                        category="token",
                        severity="error",
                        details={"issue": "unclosed_statement", "raw_message": msg},
                    )
                )
            else:
                errors.append(
                    DetectedError(
                        error_type="SyntaxError",
                        message=f"Tokenization error: {msg}.",
                        line=erow,
                        column=ecol or 1,
                        source_snippet=line_content,
                        category="token",
                        severity="error",
                        details={"issue": "token_error", "raw_message": msg},
                    )
                )
        except IndentationError as exc:
            line_content = lines[exc.lineno - 1] if exc.lineno and 1 <= exc.lineno <= len(lines) else ""
            errors.append(
                DetectedError(
                    error_type="IndentationError",
                    message=f"Indentation error: {exc.msg}.",
                    line=exc.lineno or 1,
                    column=exc.offset or 1,
                    source_snippet=line_content,
                    category="token",
                    severity="error",
                    details={"issue": "indentation_error"},
                )
            )

        return errors


class StaticASTAnalyzer(ast.NodeVisitor):
    """Static AST visitor for semantic checks: undefined variables, bad operations, arg mismatches, logical issues."""

    BUILTIN_NAMES = set(dir(builtins))

    def __init__(self, code: str):
        self.code = code
        self.lines = code.splitlines()
        self.errors: List[DetectedError] = []
        self.scope_stack: List[Dict[str, Any]] = [{"defined": set(self.BUILTIN_NAMES), "assigned": set()}]
        self.function_defs: Dict[str, Tuple[List[str], int]] = {}

    def _get_line(self, lineno: int) -> str:
        return self.lines[lineno - 1] if 1 <= lineno <= len(self.lines) else ""

    def visit_Import(self, node: ast.Import) -> None:
        for alias in node.names:
            name = alias.asname or alias.name.split(".")[0]
            self.scope_stack[-1]["defined"].add(name)
        self.generic_visit(node)

    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:
        for alias in node.names:
            name = alias.asname or alias.name
            self.scope_stack[-1]["defined"].add(name)
        self.generic_visit(node)

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self.scope_stack[-1]["defined"].add(node.name)
        arg_names = [a.arg for a in node.args.args]
        self.function_defs[node.name] = (arg_names, node.lineno)

        for default in node.args.defaults:
            if isinstance(default, (ast.List, ast.Dict, ast.Set)):
                self.errors.append(
                    DetectedError(
                        error_type="LogicalWarning",
                        message=f"Mutable default argument '{ast.unparse(default)}' in function '{node.name}'. Use None and default in body.",
                        line=node.lineno,
                        column=node.col_offset + 1,
                        source_snippet=self._get_line(node.lineno),
                        category="logical",
                        severity="warning",
                        details={"issue": "mutable_default", "function": node.name},
                    )
                )

        new_scope = {"defined": set(self.BUILTIN_NAMES) | set(arg_names), "assigned": set(arg_names)}
        self.scope_stack.append(new_scope)
        self.generic_visit(node)
        self.scope_stack.pop()

    def visit_Assign(self, node: ast.Assign) -> None:
        self.visit(node.value)
        for target in node.targets:
            if isinstance(target, ast.Name):
                self.scope_stack[-1]["defined"].add(target.id)
                self.scope_stack[-1]["assigned"].add(target.id)
            elif isinstance(target, (ast.Tuple, ast.List)):
                for elt in target.elts:
                    if isinstance(elt, ast.Name):
                        self.scope_stack[-1]["defined"].add(elt.id)
                        self.scope_stack[-1]["assigned"].add(elt.id)
            else:
                self.visit(target)

    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        if node.value:
            self.visit(node.value)
        if isinstance(node.target, ast.Name):
            self.scope_stack[-1]["defined"].add(node.target.id)

    def visit_AugAssign(self, node: ast.AugAssign) -> None:
        self.visit(node.target)
        self.visit(node.value)

    def visit_Name(self, node: ast.Name) -> None:
        if isinstance(node.ctx, ast.Load):
            is_defined = any(node.id in s["defined"] for s in reversed(self.scope_stack))
            if not is_defined:
                self.errors.append(
                    DetectedError(
                        error_type="NameError",
                        message=f"Undefined variable or name '{node.id}' is used before definition.",
                        line=node.lineno,
                        column=node.col_offset + 1,
                        source_snippet=self._get_line(node.lineno),
                        category="ast_static",
                        severity="error",
                        details={"name": node.id, "issue": "undefined_variable"},
                    )
                )

    def visit_BinOp(self, node: ast.BinOp) -> None:
        if isinstance(node.op, (ast.Div, ast.FloorDiv, ast.Mod)):
            if isinstance(node.right, ast.Constant) and node.right.value == 0:
                self.errors.append(
                    DetectedError(
                        error_type="ZeroDivisionError",
                        message="Division or modulo by literal zero detected.",
                        line=node.lineno,
                        column=node.col_offset + 1,
                        source_snippet=self._get_line(node.lineno),
                        category="ast_static",
                        severity="error",
                        details={"issue": "zero_division"},
                    )
                )

        if isinstance(node.op, ast.Add):
            left_val = node.left.value if isinstance(node.left, ast.Constant) else None
            right_val = node.right.value if isinstance(node.right, ast.Constant) else None
            if (isinstance(left_val, str) and isinstance(right_val, (int, float))) or (
                isinstance(left_val, (int, float)) and isinstance(right_val, str)
            ):
                self.errors.append(
                    DetectedError(
                        error_type="TypeError",
                        message=f"Cannot add mismatched literal types: '{type(left_val).__name__}' and '{type(right_val).__name__}'.",
                        line=node.lineno,
                        column=node.col_offset + 1,
                        source_snippet=self._get_line(node.lineno),
                        category="ast_static",
                        severity="error",
                        details={"issue": "mismatched_binary_operands", "types": [type(left_val).__name__, type(right_val).__name__]},
                    )
                )
        self.generic_visit(node)

    def visit_Compare(self, node: ast.Compare) -> None:
        for op, comp in zip(node.ops, node.comparators):
            if isinstance(op, (ast.Is, ast.IsNot)):
                if isinstance(comp, ast.Constant) and isinstance(comp.value, (int, float, str)):
                    self.errors.append(
                        DetectedError(
                            error_type="LogicalWarning",
                            message=f"Comparison with literal using '{'is' if isinstance(op, ast.Is) else 'is not'}'. Use '==' or '!=' instead.",
                            line=node.lineno,
                            column=node.col_offset + 1,
                            source_snippet=self._get_line(node.lineno),
                            category="logical",
                            severity="warning",
                            details={"issue": "is_literal_comparison"},
                        )
                    )
        self.generic_visit(node)

    def visit_Call(self, node: ast.Call) -> None:
        if isinstance(node.func, ast.Name) and node.func.id in self.function_defs:
            arg_names, def_line = self.function_defs[node.func.id]
            expected_count = len(arg_names)
            passed_count = len(node.args)
            if passed_count > expected_count:
                self.errors.append(
                    DetectedError(
                        error_type="TypeError",
                        message=f"Function '{node.func.id}' defined on line {def_line} expects {expected_count} argument(s), but {passed_count} were passed.",
                        line=node.lineno,
                        column=node.col_offset + 1,
                        source_snippet=self._get_line(node.lineno),
                        category="ast_static",
                        severity="error",
                        details={
                            "issue": "too_many_arguments",
                            "function": node.func.id,
                            "expected": expected_count,
                            "passed": passed_count,
                        },
                    )
                )
        self.generic_visit(node)


class ErrorDetector:
    """Primary Error Detection System combining AST, Tokenize, and Traceback parsing."""

    CONTROL_KEYWORDS = (
        "if", "elif", "else", "for", "while", "def", "class",
        "try", "except", "finally", "with", "async def", "async for", "async with", "match", "case"
    )

    @classmethod
    def detect_static(cls, code: str) -> List[DetectedError]:
        if not code or not code.strip():
            return []

        errors: List[DetectedError] = []
        token_errors = TokenAnalyzer.analyze(code)
        errors.extend(token_errors)

        lines = code.splitlines()
        try:
            tree = ast.parse(code, filename="<seds_editor>")
            visitor = StaticASTAnalyzer(code)
            visitor.visit(tree)
            errors.extend(visitor.errors)
        except SyntaxError as exc:
            line_no = exc.lineno or 1
            col_no = exc.offset or 1
            snippet = lines[line_no - 1] if 1 <= line_no <= len(lines) else (exc.text or "").strip()

            specific_message = exc.msg
            error_type = exc.__class__.__name__

            is_colon_issue = False
            stripped = snippet.strip()
            for kw in cls.CONTROL_KEYWORDS:
                if re.match(rf"^{kw}\b", stripped) and not stripped.endswith(":"):
                    specific_message = f"Missing colon ':' at the end of '{kw}' statement."
                    is_colon_issue = True
                    break

            has_matching_token_err = any(e.line == line_no and e.category == "token" for e in token_errors)
            if not has_matching_token_err:
                errors.append(
                    DetectedError(
                        error_type=error_type,
                        message=specific_message,
                        line=line_no,
                        column=col_no,
                        end_line=exc.end_lineno,
                        end_column=exc.end_offset,
                        source_snippet=snippet,
                        category="syntax",
                        severity="error",
                        details={
                            "issue": "missing_colon" if is_colon_issue else "syntax_error",
                            "raw_message": exc.msg,
                        },
                    )
                )

        return errors

    @classmethod
    def parse_runtime_traceback(cls, stderr: str, source_code: str = "") -> Optional[DetectedError]:
        if not stderr or not stderr.strip():
            return None

        lines = stderr.strip().splitlines()
        source_lines = source_code.splitlines() if source_code else []

        user_line_no: Optional[int] = None
        user_col_no: Optional[int] = None

        for line in lines:
            match = re.search(r'File ".*?", line (\d+)(?:, in .*)?', line)
            if match:
                user_line_no = int(match.group(1))

        for line in lines:
            if re.match(r"^\s*[\^~]+\s*$", line):
                user_col_no = line.find("^") + 1
                break

        last_line = lines[-1].strip()
        error_type = "RuntimeError"
        error_msg = last_line

        match = re.match(r"^([A-Za-z_][A-Za-z0-9_.]*):\s*(.*)$", last_line)
        if match:
            error_type = match.group(1)
            error_msg = match.group(2)
        elif "SyntaxError" in last_line:
            error_type = "SyntaxError"

        line_num = user_line_no or 1
        snippet = source_lines[line_num - 1] if source_lines and 1 <= line_num <= len(source_lines) else ""

        return DetectedError(
            error_type=error_type,
            message=error_msg,
            line=line_num,
            column=user_col_no or 1,
            source_snippet=snippet,
            category="runtime",
            severity="error",
            details={"raw_stderr": stderr},
        )

    @classmethod
    def detect_all(cls, code: str, runtime_stderr: Optional[str] = None) -> List[DetectedError]:
        errors = cls.detect_static(code)
        if runtime_stderr:
            runtime_err = cls.parse_runtime_traceback(runtime_stderr, code)
            if runtime_err:
                already_exists = any(
                    e.line == runtime_err.line and e.error_type == runtime_err.error_type for e in errors
                )
                if not already_exists:
                    errors.insert(0, runtime_err)
        return errors


# =============================================================================
# 2. AI SERVICE (OPENAI & GEMINI INTEGRATION)
# =============================================================================

class AIService:
    """Manages AI interactions with OpenAI and Gemini."""

    @classmethod
    def get_status(cls) -> Dict[str, Any]:
        openai_key = os.getenv("OPENAI_API_KEY", "").strip()
        gemini_key = os.getenv("GEMINI_API_KEY", "").strip()
        return {
            "openai_configured": bool(openai_key),
            "gemini_configured": bool(gemini_key),
            "active_provider": "openai" if openai_key else ("gemini" if gemini_key else "offline_heuristic"),
        }

    @classmethod
    def explain_and_fix(
        cls,
        error_info: Dict[str, Any],
        source_code: str,
        user_consent: bool = False,
        preferred_provider: str = "auto",
    ) -> Optional[Dict[str, Any]]:
        if not user_consent:
            return None

        status = cls.get_status()
        if not status["openai_configured"] and not status["gemini_configured"]:
            return None

        provider = status["active_provider"] if preferred_provider == "auto" else preferred_provider

        system_prompt = (
            "You are SEDS (Smart Error Detection System), an expert Python debugging assistant. "
            "Analyze the given Python error and source code, then respond strictly with a valid JSON object "
            "containing these exact keys:\n"
            "1. what: Simple summary of what the error is\n"
            "2. where: Exactly where the error starts (line & column)\n"
            "3. why: Why the error happened conceptually\n"
            "4. cause: What specifically in the code caused it\n"
            "5. affected: Which variables/statements/lines are affected\n"
            "6. how_to_fix: Clear step-by-step instructions in simple English for students\n"
            "7. corrected_code: Complete corrected Python code string\n"
            "8. confidence: High, Medium, or Low\n"
            "Never invent variable values or arbitrarily change program logic."
        )

        user_prompt = (
            f"Error Type: {error_info.get('error_type')}\n"
            f"Line: {error_info.get('line')}, Column: {error_info.get('column')}\n"
            f"Message: {error_info.get('message')}\n"
            f"Source Snippet: {error_info.get('source_snippet')}\n\n"
            f"Full Source Code:\n```python\n{source_code}\n```"
        )

        try:
            if provider == "openai" and status["openai_configured"]:
                import openai
                api_key = os.getenv("OPENAI_API_KEY", "").strip()
                model = os.getenv("OPENAI_MODEL", "gpt-4o-mini").strip()
                client = openai.OpenAI(api_key=api_key)
                response = client.chat.completions.create(
                    model=model,
                    messages=[
                        {"role": "system", "content": system_prompt},
                        {"role": "user", "content": user_prompt},
                    ],
                    response_format={"type": "json_object"},
                    temperature=0.2,
                )
                content = response.choices[0].message.content
                return json.loads(content) if content else None

            elif provider == "gemini" and status["gemini_configured"]:
                from google import genai
                api_key = os.getenv("GEMINI_API_KEY", "").strip()
                model = os.getenv("GEMINI_MODEL", "gemini-2.5-flash").strip()
                client = genai.Client(api_key=api_key)
                prompt = f"{system_prompt}\n\n{user_prompt}\nRespond strictly with JSON."
                response = client.models.generate_content(model=model, contents=prompt)
                text = (response.text or "").strip()
                if text.startswith("```json"):
                    text = text[7:]
                if text.startswith("```"):
                    text = text[3:]
                if text.endswith("```"):
                    text = text[:-3]
                return json.loads(text.strip())
        except Exception as exc:
            return {
                "ai_error": f"AI provider request failed: {exc}. Using local rule-based engine.",
                "fallback": True,
            }

        return None


# =============================================================================
# 3. 7-POINT ERROR EXPLAINER
# =============================================================================

@dataclass
class ExplanationResult:
    what: str
    where: str
    why: str
    cause: str
    affected: str
    how_to_fix: str
    corrected_code: Optional[str] = None
    confidence: str = "High"
    provider: str = "local_heuristic"

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


class ErrorExplainer:
    """Explains Python errors with 7-point beginner-friendly diagnostics."""

    @classmethod
    def explain(
        cls,
        error: DetectedError,
        source_code: str,
        user_consent: bool = False,
        preferred_provider: str = "auto",
    ) -> ExplanationResult:
        if user_consent:
            ai_data = AIService.explain_and_fix(
                error.to_dict(), source_code, user_consent=True, preferred_provider=preferred_provider
            )
            if ai_data and not ai_data.get("fallback"):
                return ExplanationResult(
                    what=ai_data.get("what", "Error detected in program execution."),
                    where=ai_data.get("where", f"Line {error.line}, Column {error.column}"),
                    why=ai_data.get("why", "The Python interpreter encountered an invalid instruction."),
                    cause=ai_data.get("cause", error.message),
                    affected=ai_data.get("affected", error.source_snippet or f"Line {error.line}"),
                    how_to_fix=ai_data.get("how_to_fix", "Review the suggested code fix."),
                    corrected_code=ai_data.get("corrected_code"),
                    confidence=ai_data.get("confidence", "High"),
                    provider=preferred_provider if preferred_provider != "auto" else "ai",
                )

        return cls._explain_locally(error, source_code)

    @classmethod
    def _explain_locally(cls, error: DetectedError, source_code: str) -> ExplanationResult:
        err_type = error.error_type
        msg = error.message
        line = error.line
        col = error.column
        lines = source_code.splitlines()
        snippet = error.source_snippet or (lines[line - 1] if 1 <= line <= len(lines) else "")
        where = f"Line {line}, Column {col}"

        if err_type == "SyntaxError":
            if "bracket" in msg.lower() or "parenthesis" in msg.lower() or "brace" in msg.lower():
                return ExplanationResult(
                    what="SyntaxError: Unclosed or mismatched bracket/parenthesis.",
                    where=where,
                    why="Python needs matching opening and closing delimiters '()', '[]', or '{}'.",
                    cause=f"The bracket was opened but Python reached the end without finding the closing partner: {msg}",
                    affected=f"Expression on line {line}: `{snippet.strip()}`",
                    how_to_fix="Add the corresponding closing bracket at the end of the data structure or call.",
                    confidence="High",
                    provider="local_heuristic",
                )
            if "colon" in msg.lower() or "expected ':'" in msg.lower():
                return ExplanationResult(
                    what="SyntaxError: Missing colon (':') at the end of statement header.",
                    where=where,
                    why="In Python, compound statements (like if, for, while, def, class) must end with a colon ':' to introduce an indented block.",
                    cause=f"The line `{snippet.strip()}` is missing a ':' at the end.",
                    affected=f"Block header on line {line}: `{snippet.strip()}`",
                    how_to_fix="Add a colon ':' at the very end of this line.",
                    confidence="High",
                    provider="local_heuristic",
                )
            if "quotation mark" in msg.lower() or "string" in msg.lower() or (error.details and error.details.get("issue") == "unclosed_string"):
                q_char = error.details.get("quote", '"') if error.details else ('"' if '"' in snippet else "'")
                q_name = "double quote" if q_char in ('"', '"""') else "single quote"
                return ExplanationResult(
                    what="SyntaxError: Unterminated string literal.",
                    where=where,
                    why="String values must be enclosed in matching single ('') or double (\"\") quotes.",
                    cause=f"A string was opened with a {q_name} ({q_char}) but not properly closed.",
                    affected=f"String literal on line {line}: `{snippet.strip()}`",
                    how_to_fix=f"Add the closing {q_name} ({q_char}) before closing delimiters or at the end of the line.",
                    confidence="High",
                    provider="local_heuristic",
                )
            return ExplanationResult(
                what="SyntaxError: Invalid Python syntax.",
                where=where,
                why="The code violates Python grammar rules, so Python cannot parse or understand it.",
                cause=f"Python encountered an unexpected token or structure: {msg}",
                affected=f"Statement on line {line}: `{snippet.strip()}`",
                how_to_fix="Check for missing punctuation, improper operators, or misspelled keywords on this line.",
                confidence="High",
                provider="local_heuristic",
            )

        if err_type in ("IndentationError", "TabError"):
            return ExplanationResult(
                what=f"{err_type}: Indentation problem in code block.",
                where=where,
                why="Python uses indentation (spacing) to determine which statements belong to which block or function.",
                cause="Inconsistent spaces/tabs or unexpected indentation level: " + msg,
                affected=f"Line {line}: `{snippet}`",
                how_to_fix="Use consistent 4 spaces per indentation level and avoid mixing tabs and spaces.",
                confidence="High",
                provider="local_heuristic",
            )

        if err_type == "NameError":
            match = re.search(r"name ['\"]([^'\"]+)['\"]", msg)
            name = match.group(1) if match else "variable"
            tokens = set(re.findall(r"\b[A-Za-z_][A-Za-z0-9_]*\b", source_code))
            tokens.discard(name)
            closest = difflib.get_close_matches(name, list(tokens), n=1, cutoff=0.7)
            fix_tip = (
                f"Did you mean '{closest[0]}' instead of '{name}'?"
                if closest
                else f"Define '{name}' before using it (e.g. `{name} = ...`) or verify spelling."
            )
            return ExplanationResult(
                what=f"NameError: Name '{name}' is not defined.",
                where=where,
                why="Python tried to evaluate an identifier that has not been assigned a value or imported.",
                cause=f"The variable or function '{name}' does not exist in the current scope.",
                affected=f"Usage of '{name}' on line {line}: `{snippet.strip()}`",
                how_to_fix=fix_tip,
                confidence="High",
                provider="local_heuristic",
            )

        if err_type == "TypeError":
            return ExplanationResult(
                what="TypeError: Incompatible data types in operation or function call.",
                where=where,
                why="The operation or function was invoked with values whose types are incompatible.",
                cause=msg,
                affected=f"Operation on line {line}: `{snippet.strip()}`",
                how_to_fix="Convert the operands to compatible types (e.g. using str() or int()) or check argument count.",
                confidence="High",
                provider="local_heuristic",
            )

        if err_type == "IndexError":
            return ExplanationResult(
                what="IndexError: Sequence index out of range.",
                where=where,
                why="You attempted to access an item at an index number that exceeds the length of the list/sequence.",
                cause="The list does not have an element at this position: " + msg,
                affected=f"Index access on line {line}: `{snippet.strip()}`",
                how_to_fix="Check `len(sequence)` before accessing, or verify zero-based indexing (remember index starts at 0).",
                confidence="High",
                provider="local_heuristic",
            )

        if err_type == "ZeroDivisionError":
            return ExplanationResult(
                what="ZeroDivisionError: Division or modulo by zero.",
                where=where,
                why="In mathematics and computer science, dividing a number by zero is undefined.",
                cause="The denominator of a division ('/' or '//') or modulo ('%') evaluated to zero.",
                affected=f"Division expression on line {line}: `{snippet.strip()}`",
                how_to_fix="Check if the divisor is non-zero before dividing: `if divisor != 0: ...`",
                confidence="High",
                provider="local_heuristic",
            )

        if err_type == "KeyError":
            match = re.search(r"['\"]?([^'\"]+)['\"]?", msg)
            key = match.group(1) if match else "key"
            return ExplanationResult(
                what=f"KeyError: Dictionary key {key} not found.",
                where=where,
                why="You accessed a dictionary using a key that does not exist in the dictionary map.",
                cause=f"The key {key} is missing from the dictionary.",
                affected=f"Dictionary access on line {line}: `{snippet.strip()}`",
                how_to_fix=f"Use `dict.get({key}, default_value)` or verify that the key exists with `if {key} in dict:`.",
                confidence="High",
                provider="local_heuristic",
            )

        if err_type == "ValueError":
            return ExplanationResult(
                what="ValueError: Inappropriate argument value.",
                where=where,
                why="The function received an argument that has the right type but an inappropriate value.",
                cause=msg,
                affected=f"Call on line {line}: `{snippet.strip()}`",
                how_to_fix="Validate and sanitize user input before passing it into type-casting or parsing functions.",
                confidence="High",
                provider="local_heuristic",
            )

        if err_type == "AttributeError":
            return ExplanationResult(
                what="AttributeError: Object does not have requested attribute or method.",
                where=where,
                why="Python tried to access a property or method that is not defined on that object type.",
                cause=msg,
                affected=f"Attribute access on line {line}: `{snippet.strip()}`",
                how_to_fix="Check the object's actual type and check for misspellings in the method/attribute name.",
                confidence="High",
                provider="local_heuristic",
            )

        if err_type in ("ImportError", "ModuleNotFoundError"):
            return ExplanationResult(
                what=f"{err_type}: Cannot import required module or name.",
                where=where,
                why="Python could not find the specified package in the environment's search path.",
                cause=msg,
                affected=f"Import statement on line {line}: `{snippet.strip()}`",
                how_to_fix="Install the missing package via pip (e.g. `pip install <package>`) or check the module name.",
                confidence="High",
                provider="local_heuristic",
            )

        return ExplanationResult(
            what=f"{err_type}: Program encountered an error.",
            where=where,
            why="An exception interrupted normal execution.",
            cause=msg,
            affected=f"Line {line}: `{snippet.strip()}`",
            how_to_fix="Examine the traceback details and verify the operation logic on this line.",
            confidence="Medium",
            provider="local_heuristic",
        )


# =============================================================================
# 4. AUTOMATIC CODE REPAIR & VALIDATION ENGINE
# =============================================================================

@dataclass
class FixResult:
    is_valid: bool
    original_code: str
    fixed_code: Optional[str]
    diff: str
    changes_description: str
    requires_user_review: bool = False
    validation_notes: str = ""
    provider: str = "local_rule_engine"

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


class AutoFixer:
    """Intelligent repair engine that generates and validates code patches."""

    @classmethod
    def generate_fix(
        cls,
        error: DetectedError,
        source_code: str,
        user_consent: bool = False,
        preferred_provider: str = "auto",
    ) -> FixResult:
        if user_consent:
            ai_data = AIService.explain_and_fix(
                error.to_dict(), source_code, user_consent=True, preferred_provider=preferred_provider
            )
            if ai_data and ai_data.get("corrected_code") and not ai_data.get("fallback"):
                candidate = ai_data["corrected_code"].strip()
                val_ok, note = cls.validate_candidate(candidate)
                if val_ok:
                    diff_text = cls._create_diff(source_code, candidate)
                    return FixResult(
                        is_valid=True,
                        original_code=source_code,
                        fixed_code=candidate,
                        diff=diff_text,
                        changes_description=ai_data.get("how_to_fix", "AI generated automatic fix."),
                        requires_user_review=ai_data.get("confidence") != "High",
                        validation_notes="Passed Python syntax and AST compilation checks.",
                        provider="ai",
                    )

        return cls._generate_local_fix(error, source_code)

    @classmethod
    def validate_candidate(cls, candidate: str) -> Tuple[bool, str]:
        if not candidate or not candidate.strip():
            return False, "Candidate code is empty."
        try:
            ast.parse(candidate, filename="<seds_candidate>")
            compile(candidate, "<seds_candidate>", "exec")
            return True, "Code passed AST and compile validation successfully."
        except (SyntaxError, ValueError) as exc:
            return False, f"Syntax validation failed: {exc}"

    @classmethod
    def _create_diff(cls, original: str, fixed: str) -> str:
        orig_lines = original.splitlines(keepends=True)
        fixed_lines = fixed.splitlines(keepends=True)
        diff = difflib.unified_diff(
            orig_lines,
            fixed_lines,
            fromfile="Original Code",
            tofile="Suggested Fix",
            lineterm="",
        )
        return "".join(diff)

    @classmethod
    def _fix_unclosed_string(
        cls,
        source_code: str,
        line_idx: int,
        quote_hint: Optional[str] = None,
    ) -> Optional[tuple[str, str]]:
        lines = source_code.splitlines()
        if not (0 <= line_idx < len(lines)):
            return None
        target = lines[line_idx]

        quotes_to_try: list[str] = []
        if quote_hint in ('"', "'", '"""', "'''"):
            quotes_to_try.append(quote_hint)
        if target.count('"') % 2 != 0:
            quotes_to_try.append('"')
        if target.count("'") % 2 != 0:
            quotes_to_try.append("'")
        for q in ('"', "'"):
            if q not in quotes_to_try:
                quotes_to_try.append(q)

        candidates: list[tuple[str, str]] = []
        for q in quotes_to_try:
            match_trailing = re.search(r"([\s,;:)}\]]+)$", target)
            if match_trailing:
                pos = match_trailing.start()
                cand_line = target[:pos] + q + target[pos:]
                candidates.append((cand_line, f"Closed string literal with {q} before trailing delimiter."))

            cand_line_end = target.rstrip() + q
            candidates.append((cand_line_end, f"Added missing closing quote {q} at end of statement."))

            open_parens = max(0, target.count("(") - target.count(")"))
            open_squares = max(0, target.count("[") - target.count("]"))
            open_curlies = max(0, target.count("{") - target.count("}"))
            brackets = (")" * open_parens) + ("]" * open_squares) + ("}" * open_curlies)
            if brackets:
                cand_combined = target.rstrip() + q + brackets
                candidates.append((cand_combined, f"Closed string with {q} and completed matching brackets."))

            for idx in range(len(target) - 1, -1, -1):
                if target[idx] in (")", "]", "}", ",", ":"):
                    cand_mid = target[:idx] + q + target[idx:]
                    candidates.append((cand_mid, f"Closed string with {q}."))

        for cand_line, desc in candidates:
            cand_lines = list(lines)
            cand_lines[line_idx] = cand_line
            candidate_code = "\n".join(cand_lines) + ("\n" if source_code.endswith("\n") else "")
            val_ok, note = cls.validate_candidate(candidate_code)
            if val_ok:
                return candidate_code, desc

        return None

    @classmethod
    def _generate_local_fix(cls, error: DetectedError, source_code: str) -> FixResult:
        lines = source_code.splitlines()
        line_idx = error.line - 1 if 1 <= error.line <= len(lines) else None

        # Case 1: Indentation / Tab normalization
        if error.error_type in ("IndentationError", "TabError") or (error.details and error.details.get("issue") == "mixed_tabs_spaces"):
            candidate = source_code.expandtabs(4)
            if candidate != source_code:
                val_ok, note = cls.validate_candidate(candidate)
                if val_ok:
                    return FixResult(
                        is_valid=True,
                        original_code=source_code,
                        fixed_code=candidate,
                        diff=cls._create_diff(source_code, candidate),
                        changes_description="Normalized tab indentation to consistent 4 spaces.",
                        requires_user_review=False,
                        validation_notes=note,
                    )

        # Case 2: Missing closing bracket
        if error.details and error.details.get("issue") in ("unclosed_bracket", "unclosed_statement") and line_idx is not None:
            expected_char = error.details.get("expected")
            if not expected_char and "bracket" in error.message.lower():
                if "square" in error.message.lower() or "[" in error.source_snippet:
                    expected_char = "]"
                elif "curly" in error.message.lower() or "{" in error.source_snippet:
                    expected_char = "}"
                else:
                    expected_char = ")"

            if expected_char:
                candidate_lines = list(lines)
                candidate_lines[line_idx] = candidate_lines[line_idx] + expected_char
                candidate = "\n".join(candidate_lines) + ("\n" if source_code.endswith("\n") else "")
                val_ok, note = cls.validate_candidate(candidate)
                if val_ok:
                    return FixResult(
                        is_valid=True,
                        original_code=source_code,
                        fixed_code=candidate,
                        diff=cls._create_diff(source_code, candidate),
                        changes_description=f"Appended missing closing bracket '{expected_char}' on line {error.line}.",
                        requires_user_review=False,
                        validation_notes=note,
                    )

        # Case 3: Missing colon on block header
        if (error.details and error.details.get("issue") == "missing_colon" or "colon" in error.message.lower()) and line_idx is not None:
            target = lines[line_idx].rstrip()
            if not target.endswith(":"):
                candidate_lines = list(lines)
                candidate_lines[line_idx] = target + ":"
                candidate = "\n".join(candidate_lines) + ("\n" if source_code.endswith("\n") else "")
                val_ok, note = cls.validate_candidate(candidate)
                if val_ok:
                    return FixResult(
                        is_valid=True,
                        original_code=source_code,
                        fixed_code=candidate,
                        diff=cls._create_diff(source_code, candidate),
                        changes_description=f"Added missing colon ':' to block header on line {error.line}.",
                        requires_user_review=False,
                        validation_notes=note,
                    )

        # Case 4: Missing closing quote in string literal (unterminated string literal)
        is_string_err = (
            (error.details and error.details.get("issue") == "unclosed_string")
            or "unterminated string" in error.message.lower()
            or "unclosed string" in error.message.lower()
            or "quotation mark" in error.message.lower()
            or (error.details and "unterminated string" in str(error.details.get("raw_message", "")).lower())
        )
        if is_string_err and line_idx is not None:
            quote_hint = error.details.get("quote") if error.details else None
            fix_res = cls._fix_unclosed_string(source_code, line_idx, quote_hint)
            if fix_res:
                fixed_code, desc = fix_res
                return FixResult(
                    is_valid=True,
                    original_code=source_code,
                    fixed_code=fixed_code,
                    diff=cls._create_diff(source_code, fixed_code),
                    changes_description=desc,
                    requires_user_review=False,
                    validation_notes="Code passed AST and compile validation successfully.",
                )

        # Case 5: NameError - missing import or misspelled identifier
        if error.error_type == "NameError" and line_idx is not None:
            unknown_name = None
            if error.details and "name" in error.details:
                unknown_name = error.details["name"]
            else:
                match = re.search(r"name ['\"]([^'\"]+)['\"]", error.message)
                if match:
                    unknown_name = match.group(1)

            COMMON_STDLIB = {
                "math", "sys", "os", "json", "random", "re", "time", "datetime",
                "pathlib", "collections", "itertools", "functools", "urllib", "sqlite3",
                "csv", "hashlib", "copy", "shutil", "io", "string", "subprocess", "logging"
            }
            if unknown_name in COMMON_STDLIB:
                candidate = f"import {unknown_name}\n" + source_code
                val_ok, note = cls.validate_candidate(candidate)
                if val_ok:
                    return FixResult(
                        is_valid=True,
                        original_code=source_code,
                        fixed_code=candidate,
                        diff=cls._create_diff(source_code, candidate),
                        changes_description=f"Added missing standard library import 'import {unknown_name}'.",
                        requires_user_review=False,
                        validation_notes=note,
                    )

            if unknown_name:
                identifiers = set(re.findall(r"\b[A-Za-z_][A-Za-z0-9_]*\b", source_code))
                identifiers.update(dir(builtins))
                identifiers.discard(unknown_name)
                close_matches = difflib.get_close_matches(unknown_name, sorted(identifiers), n=1, cutoff=0.7)
                if close_matches:
                    replacement = close_matches[0]
                    target_line = lines[line_idx]
                    corrected_line = re.sub(rf"\b{re.escape(unknown_name)}\b", replacement, target_line, count=1)
                    candidate_lines = list(lines)
                    candidate_lines[line_idx] = corrected_line
                    candidate = "\n".join(candidate_lines) + ("\n" if source_code.endswith("\n") else "")
                    val_ok, note = cls.validate_candidate(candidate)
                    if val_ok:
                        return FixResult(
                            is_valid=True,
                            original_code=source_code,
                            fixed_code=candidate,
                            diff=cls._create_diff(source_code, candidate),
                            changes_description=f"Corrected likely misspelled name '{unknown_name}' to '{replacement}' on line {error.line}.",
                            requires_user_review=False,
                            validation_notes=note,
                        )

        # Case 6: SyntaxError - Assignment in condition (if x = 5 -> if x == 5)
        if error.error_type == "SyntaxError" and line_idx is not None:
            target = lines[line_idx]
            match_assign = re.search(r"^(?P<indent>\s*(?:if|elif|while)\s+)(?P<expr>[^=:\n]+)=(?P<rest>[^=:\n]+:.*)$", target)
            if match_assign:
                corrected_line = match_assign.group("indent") + match_assign.group("expr").rstrip() + " == " + match_assign.group("rest").lstrip()
                cand_lines = list(lines)
                cand_lines[line_idx] = corrected_line
                candidate = "\n".join(cand_lines) + ("\n" if source_code.endswith("\n") else "")
                val_ok, note = cls.validate_candidate(candidate)
                if val_ok:
                    return FixResult(
                        is_valid=True,
                        original_code=source_code,
                        fixed_code=candidate,
                        diff=cls._create_diff(source_code, candidate),
                        changes_description=f"Replaced assignment '=' with comparison '==' in condition on line {error.line}.",
                        requires_user_review=False,
                        validation_notes=note,
                    )

        # Case 7: SyntaxError - C-style logical operators (&&, ||, ===, !==, true, false, null)
        if error.error_type == "SyntaxError" and line_idx is not None:
            target = lines[line_idx]
            corrected = target
            corrected = re.sub(r"===+", "==", corrected)
            corrected = re.sub(r"!==+", "!=", corrected)
            corrected = re.sub(r"\s*&&\s*", " and ", corrected)
            corrected = re.sub(r"\s*\|\|\s*", " or ", corrected)
            corrected = re.sub(r"\btrue\b", "True", corrected)
            corrected = re.sub(r"\bfalse\b", "False", corrected)
            corrected = re.sub(r"\bnull\b", "None", corrected)
            if corrected != target:
                cand_lines = list(lines)
                cand_lines[line_idx] = corrected
                candidate = "\n".join(cand_lines) + ("\n" if source_code.endswith("\n") else "")
                val_ok, note = cls.validate_candidate(candidate)
                if val_ok:
                    return FixResult(
                        is_valid=True,
                        original_code=source_code,
                        fixed_code=candidate,
                        diff=cls._create_diff(source_code, candidate),
                        changes_description=f"Converted C-style logical operators to Python equivalents ('and', 'or', '==') on line {error.line}.",
                        requires_user_review=False,
                        validation_notes=note,
                    )

        # Case 8: SyntaxError - Python 2 style print statement without parens
        if error.error_type == "SyntaxError" and line_idx is not None:
            target = lines[line_idx]
            match_print = re.match(r"^(?P<indent>\s*)print\s+(?P<args>[^()]+)$", target)
            if match_print:
                corrected_line = f"{match_print.group('indent')}print({match_print.group('args').strip()})"
                cand_lines = list(lines)
                cand_lines[line_idx] = corrected_line
                candidate = "\n".join(cand_lines) + ("\n" if source_code.endswith("\n") else "")
                val_ok, note = cls.validate_candidate(candidate)
                if val_ok:
                    return FixResult(
                        is_valid=True,
                        original_code=source_code,
                        fixed_code=candidate,
                        diff=cls._create_diff(source_code, candidate),
                        changes_description=f"Wrapped print statement arguments in parentheses on line {error.line}.",
                        requires_user_review=False,
                        validation_notes=note,
                    )

        # Case 9: ZeroDivisionError
        if error.error_type == "ZeroDivisionError" and line_idx is not None:
            target_line = lines[line_idx]
            match = re.search(r"(?P<num>[A-Za-z0-9_.]+)\s*/\s*(?P<denom>[A-Za-z0-9_.]+)", target_line)
            if match:
                num = match.group("num")
                denom = match.group("denom")
                safe_expr = f"({num} / {denom} if {denom} != 0 else 0)"
                corrected_line = target_line[: match.start()] + safe_expr + target_line[match.end() :]
                candidate_lines = list(lines)
                candidate_lines[line_idx] = corrected_line
                candidate = "\n".join(candidate_lines) + ("\n" if source_code.endswith("\n") else "")
                val_ok, note = cls.validate_candidate(candidate)
                if val_ok:
                    return FixResult(
                        is_valid=True,
                        original_code=source_code,
                        fixed_code=candidate,
                        diff=cls._create_diff(source_code, candidate),
                        changes_description=f"Guarded division against zero on line {error.line} (returns 0 if denominator is 0).",
                        requires_user_review=True,
                        validation_notes="Please confirm whether returning 0 when divisor is zero matches your application logic.",
                    )

        # Case 10: TypeError - string concatenation with int/float
        if error.error_type == "TypeError" and line_idx is not None:
            target = lines[line_idx]
            if "can only concatenate str" in error.message or "unsupported operand type(s) for +" in error.message:
                match_plus = re.search(r"(\+\s*)([A-Za-z_][A-Za-z0-9_.]*)", target)
                if match_plus:
                    prefix = target[: match_plus.start()]
                    var = match_plus.group(2)
                    suffix = target[match_plus.end() :]
                    corrected_line = f"{prefix}+ str({var}){suffix}"
                    cand_lines = list(lines)
                    cand_lines[line_idx] = corrected_line
                    candidate = "\n".join(cand_lines) + ("\n" if source_code.endswith("\n") else "")
                    val_ok, note = cls.validate_candidate(candidate)
                    if val_ok:
                        return FixResult(
                            is_valid=True,
                            original_code=source_code,
                            fixed_code=candidate,
                            diff=cls._create_diff(source_code, candidate),
                            changes_description=f"Wrapped non-string variable '{var}' in str() for safe concatenation on line {error.line}.",
                            requires_user_review=False,
                            validation_notes=note,
                        )

        # Case 11: KeyError - dictionary key lookup
        if error.error_type == "KeyError" and line_idx is not None:
            target = lines[line_idx]
            match_key = re.search(r"(\b[A-Za-z_][A-Za-z0-9_.]*)\[(['\"][^'\"]+['\"])\]", target)
            if match_key:
                dict_name = match_key.group(1)
                key_expr = match_key.group(2)
                replacement = f"{dict_name}.get({key_expr})"
                corrected_line = target[: match_key.start()] + replacement + target[match_key.end() :]
                cand_lines = list(lines)
                cand_lines[line_idx] = corrected_line
                candidate = "\n".join(cand_lines) + ("\n" if source_code.endswith("\n") else "")
                val_ok, note = cls.validate_candidate(candidate)
                if val_ok:
                    return FixResult(
                        is_valid=True,
                        original_code=source_code,
                        fixed_code=candidate,
                        diff=cls._create_diff(source_code, candidate),
                        changes_description=f"Replaced direct dictionary key lookup {dict_name}[{key_expr}] with safe {dict_name}.get({key_expr}) on line {error.line}.",
                        requires_user_review=True,
                        validation_notes="Returns None instead of raising KeyError if key is missing.",
                    )

        # Case 12: IndexError - list index out of range
        if error.error_type == "IndexError" and line_idx is not None:
            target = lines[line_idx]
            match_idx = re.search(r"(\b[A-Za-z_][A-Za-z0-9_.]*)\[([A-Za-z0-9_.]+)\]", target)
            if match_idx:
                list_name = match_idx.group(1)
                idx_expr = match_idx.group(2)
                safe_expr = f"({list_name}[{idx_expr}] if len({list_name}) > {idx_expr} else None)"
                corrected_line = target[: match_idx.start()] + safe_expr + target[match_idx.end() :]
                cand_lines = list(lines)
                cand_lines[line_idx] = corrected_line
                candidate = "\n".join(cand_lines) + ("\n" if source_code.endswith("\n") else "")
                val_ok, note = cls.validate_candidate(candidate)
                if val_ok:
                    return FixResult(
                        is_valid=True,
                        original_code=source_code,
                        fixed_code=candidate,
                        diff=cls._create_diff(source_code, candidate),
                        changes_description=f"Added bounds check guard for {list_name}[{idx_expr}] on line {error.line}.",
                        requires_user_review=True,
                        validation_notes="Guards against IndexError by validating index against list length.",
                    )

        # Case 13: AttributeError - misspelled method or attribute
        if error.error_type == "AttributeError" and line_idx is not None:
            target = lines[line_idx]
            match_attr = re.search(r"object has no attribute ['\"]([^'\"]+)['\"]", error.message)
            if match_attr:
                unknown_attr = match_attr.group(1)
                KNOWN_METHODS = [
                    "append", "extend", "insert", "remove", "pop", "clear", "index", "count",
                    "sort", "reverse", "copy", "strip", "lstrip", "rstrip", "lower", "upper",
                    "capitalize", "title", "replace", "split", "rsplit", "join", "find",
                    "rfind", "startswith", "endswith", "isalpha", "isdigit", "isalnum",
                    "keys", "values", "items", "get", "update", "setdefault", "add", "discard"
                ]
                matches = difflib.get_close_matches(unknown_attr, KNOWN_METHODS, n=1, cutoff=0.6)
                if matches:
                    replacement = matches[0]
                    corrected_line = re.sub(rf"\b{re.escape(unknown_attr)}\b", replacement, target, count=1)
                    cand_lines = list(lines)
                    cand_lines[line_idx] = corrected_line
                    candidate = "\n".join(cand_lines) + ("\n" if source_code.endswith("\n") else "")
                    val_ok, note = cls.validate_candidate(candidate)
                    if val_ok:
                        return FixResult(
                            is_valid=True,
                            original_code=source_code,
                            fixed_code=candidate,
                            diff=cls._create_diff(source_code, candidate),
                            changes_description=f"Corrected misspelled method '.{unknown_attr}' to '.{replacement}' on line {error.line}.",
                            requires_user_review=False,
                            validation_notes=note,
                        )

        return FixResult(
            is_valid=False,
            original_code=source_code,
            fixed_code=None,
            diff="",
            changes_description="Automatic repair could not infer developer intent with 100% certainty.",
            requires_user_review=True,
            validation_notes="Please consult the 7-point AI Error Explanation to make the manual adjustment.",
        )


# =============================================================================
# 5. ISOLATED CODE EXECUTION SANDBOX
# =============================================================================

DEFAULT_TIMEOUT = float(os.getenv("EXECUTION_TIMEOUT_SECONDS", "5.0"))
MAX_OUTPUT_BYTES = int(os.getenv("MAX_OUTPUT_BYTES", "65536"))

SENSITIVE_PATTERNS = (
    "KEY", "SECRET", "TOKEN", "PASS", "CREDENTIAL", "API",
    "OPENAI", "GEMINI", "AUTH", "AWS", "SSH", "AGY", "SESSION"
)


@dataclass
class ExecutionResult:
    stdout: str
    stderr: str
    exit_code: int
    duration_ms: float
    timed_out: bool = False
    sandbox_mode: str = "restricted_local_process"
    security_notice: str = ""

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


class CodeRunner:
    """Controls isolated code execution with scrubbed environment and resource boundaries."""

    @classmethod
    def _get_scrubbed_env(cls) -> Dict[str, str]:
        safe_keys = {
            "SYSTEMROOT", "WINDIR", "PATH", "TEMP", "TMP", "PATHEXT",
            "USERPROFILE", "LOCALAPPDATA", "LANG", "LC_ALL"
        }
        clean_env: Dict[str, str] = {}
        for k, v in os.environ.items():
            k_upper = k.upper()
            if any(token in k_upper for token in SENSITIVE_PATTERNS):
                continue
            if k_upper in safe_keys:
                clean_env[k] = v

        clean_env["PYTHONUNBUFFERED"] = "1"
        clean_env["PYTHONDONTWRITEBYTECODE"] = "1"
        return clean_env

    @classmethod
    def run_code(cls, source_code: str, timeout: float = DEFAULT_TIMEOUT) -> ExecutionResult:
        start_time = time.perf_counter()
        temp_dir = tempfile.mkdtemp(prefix="seds_sandbox_")
        script_path = Path(temp_dir) / "main.py"

        try:
            with open(script_path, "w", encoding="utf-8", newline="\n") as f:
                f.write(source_code)

            clean_env = cls._get_scrubbed_env()
            proc = subprocess.run(
                [sys.executable, "-I", str(script_path)],
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                cwd=temp_dir,
                env=clean_env,
                timeout=timeout,
            )
            elapsed = (time.perf_counter() - start_time) * 1000
            stdout = proc.stdout[:MAX_OUTPUT_BYTES]
            stderr = proc.stderr[:MAX_OUTPUT_BYTES]

            return ExecutionResult(
                stdout=stdout,
                stderr=stderr,
                exit_code=proc.returncode,
                duration_ms=round(elapsed, 2),
                timed_out=False,
                sandbox_mode="restricted_local_process",
                security_notice="Executed in isolated disposable directory with scrubbed environment (secrets stripped).",
            )
        except subprocess.TimeoutExpired:
            elapsed = (time.perf_counter() - start_time) * 1000
            return ExecutionResult(
                stdout="",
                stderr=f"Execution Timed Out: Program exceeded {timeout} seconds time limit.",
                exit_code=-1,
                duration_ms=round(elapsed, 2),
                timed_out=True,
                sandbox_mode="restricted_local_process",
                security_notice="Execution halted by watchdog timeout limit.",
            )
        except Exception as exc:
            elapsed = (time.perf_counter() - start_time) * 1000
            return ExecutionResult(
                stdout="",
                stderr=f"Execution Failed: {exc}",
                exit_code=-1,
                duration_ms=round(elapsed, 2),
                timed_out=False,
                sandbox_mode="restricted_local_process",
                security_notice=f"Runner encounter: {exc}",
            )
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)


# =============================================================================
# 6. MULTI-FILE PROJECT SCANNER
# =============================================================================

EXCLUDED_DIRS: Set[str] = {
    ".git", ".venv", "venv", "__pycache__", "node_modules",
    ".idea", ".vscode", "build", "dist", ".pytest_cache", ".ruff_cache"
}


@dataclass
class FileScanResult:
    file_path: str
    relative_path: str
    status: str  # "PASS" | "ERROR" | "WARNING"
    error_count: int
    errors: List[Dict[str, Any]]

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


class ProjectScanner:
    """Recursively scans Python projects for syntax, token, and semantic issues."""

    @classmethod
    def scan_directory(cls, folder_path: str) -> Dict[str, Any]:
        start_time = time.perf_counter()
        folder = Path(folder_path).resolve()

        if not folder.exists() or not folder.is_dir():
            raise ValueError(f"Directory not found or invalid: {folder_path}")

        file_results: List[FileScanResult] = []
        passed_count = 0
        failed_count = 0

        for root, dirs, filenames in os.walk(folder):
            dirs[:] = [d for d in dirs if d not in EXCLUDED_DIRS]

            for fname in filenames:
                if not fname.endswith(".py"):
                    continue

                full_path = Path(root) / fname
                rel_path = str(full_path.relative_to(folder))

                try:
                    with open(full_path, "r", encoding="utf-8", errors="replace") as f:
                        content = f.read()

                    detected_errors = ErrorDetector.detect_static(content)
                    has_errors = any(e.severity == "error" for e in detected_errors)

                    enriched_errors: List[Dict[str, Any]] = []
                    for err in detected_errors:
                        expl = ErrorExplainer.explain(err, content, user_consent=False)
                        item = err.to_dict()
                        item["explanation"] = expl.to_dict()
                        enriched_errors.append(item)

                    if has_errors:
                        failed_count += 1
                        status = "ERROR"
                    elif detected_errors:
                        passed_count += 1
                        status = "WARNING"
                    else:
                        passed_count += 1
                        status = "PASS"

                    file_results.append(
                        FileScanResult(
                            file_path=str(full_path),
                            relative_path=rel_path,
                            status=status,
                            error_count=len(enriched_errors),
                            errors=enriched_errors,
                        )
                    )
                except Exception as exc:
                    failed_count += 1
                    file_results.append(
                        FileScanResult(
                            file_path=str(full_path),
                            relative_path=rel_path,
                            status="ERROR",
                            error_count=1,
                            errors=[{
                                "error_type": "ReadError",
                                "message": f"Failed to read/scan file: {exc}",
                                "line": 1,
                                "column": 1,
                                "severity": "error",
                            }],
                        )
                    )

        duration = round((time.perf_counter() - start_time) * 1000, 2)
        return {
            "folder_path": str(folder),
            "total_files": len(file_results),
            "passed_files": passed_count,
            "failed_files": failed_count,
            "duration_ms": duration,
            "files": [f.to_dict() for f in file_results],
        }


# =============================================================================
# 7. SQLITE DATABASE PERSISTENCE
# =============================================================================

DB_PATH = Path("seds.db")


class Database:
    """SQLite database manager for SEDS."""

    @classmethod
    def get_connection(cls) -> sqlite3.Connection:
        conn = sqlite3.connect(str(DB_PATH))
        conn.row_factory = sqlite3.Row
        return conn

    @classmethod
    def init_db(cls) -> None:
        with cls.get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute(
                """
                CREATE TABLE IF NOT EXISTS sessions (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    title TEXT NOT NULL,
                    source_code TEXT NOT NULL,
                    error_type TEXT,
                    error_line INTEGER,
                    error_message TEXT,
                    applied_fix TEXT,
                    execution_output TEXT,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                )
                """
            )
            cursor.execute(
                """
                CREATE TABLE IF NOT EXISTS error_history (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    session_id INTEGER,
                    error_type TEXT NOT NULL,
                    error_message TEXT NOT NULL,
                    line INTEGER,
                    column INTEGER,
                    source_snippet TEXT,
                    fixed_successfully BOOLEAN DEFAULT 0,
                    provider_used TEXT,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    FOREIGN KEY(session_id) REFERENCES sessions(id)
                )
                """
            )
            cursor.execute(
                """
                CREATE TABLE IF NOT EXISTS project_scans (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    folder_path TEXT NOT NULL,
                    total_files INTEGER NOT NULL,
                    passed_files INTEGER NOT NULL,
                    failed_files INTEGER NOT NULL,
                    report_json TEXT NOT NULL,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                )
                """
            )
            conn.commit()

    @classmethod
    def save_session(
        cls,
        title: str,
        source_code: str,
        error_type: Optional[str] = None,
        error_line: Optional[int] = None,
        error_message: Optional[str] = None,
        applied_fix: Optional[str] = None,
        execution_output: Optional[str] = None,
    ) -> int:
        with cls.get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute(
                """
                INSERT INTO sessions (title, source_code, error_type, error_line, error_message, applied_fix, execution_output)
                VALUES (?, ?, ?, ?, ?, ?, ?)
                """,
                (title, source_code, error_type, error_line, error_message, applied_fix, execution_output),
            )
            conn.commit()
            return cursor.lastrowid

    @classmethod
    def log_error(
        cls,
        error_type: str,
        error_message: str,
        line: int,
        column: int = 1,
        source_snippet: str = "",
        session_id: Optional[int] = None,
        fixed_successfully: bool = False,
        provider_used: str = "local",
    ) -> int:
        with cls.get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute(
                """
                INSERT INTO error_history (session_id, error_type, error_message, line, column, source_snippet, fixed_successfully, provider_used)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (session_id, error_type, error_message, line, column, source_snippet, 1 if fixed_successfully else 0, provider_used),
            )
            conn.commit()
            return cursor.lastrowid

    @classmethod
    def save_scan(cls, folder_path: str, total_files: int, passed_files: int, failed_files: int, report_data: Dict[str, Any]) -> int:
        with cls.get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute(
                """
                INSERT INTO project_scans (folder_path, total_files, passed_files, failed_files, report_json)
                VALUES (?, ?, ?, ?, ?)
                """,
                (folder_path, total_files, passed_files, failed_files, json.dumps(report_data)),
            )
            conn.commit()
            return cursor.lastrowid

    @classmethod
    def get_recent_sessions(cls, limit: int = 25) -> List[Dict[str, Any]]:
        with cls.get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT * FROM sessions ORDER BY created_at DESC LIMIT ?", (limit,))
            return [dict(row) for row in cursor.fetchall()]

    @classmethod
    def get_scan_history(cls, limit: int = 10) -> List[Dict[str, Any]]:
        with cls.get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT id, folder_path, total_files, passed_files, failed_files, created_at FROM project_scans ORDER BY created_at DESC LIMIT ?", (limit,))
            return [dict(row) for row in cursor.fetchall()]

    @classmethod
    def get_analytics(cls) -> Dict[str, Any]:
        with cls.get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT COUNT(*) FROM sessions")
            total_sessions = cursor.fetchone()[0]
            cursor.execute("SELECT COUNT(*) FROM error_history")
            total_errors = cursor.fetchone()[0]
            cursor.execute("SELECT COUNT(*) FROM error_history WHERE fixed_successfully = 1")
            fixed_errors = cursor.fetchone()[0]
            cursor.execute("SELECT error_type, COUNT(*) as count FROM error_history GROUP BY error_type ORDER BY count DESC LIMIT 5")
            top_errors = [dict(row) for row in cursor.fetchall()]
            return {
                "total_sessions": total_sessions,
                "total_errors_detected": total_errors,
                "fixes_applied": fixed_errors,
                "top_errors": top_errors,
            }


# =============================================================================
# 8. EMBEDDED WEB USER INTERFACE (HTML, CSS, JS)
# =============================================================================

HTML_PAGE = """<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Smart Error Detection System (SEDS) 2.0</title>
  <link rel="stylesheet" href="/style.css">
  <link rel="preconnect" href="https://fonts.googleapis.com">
  <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
  <link href="https://fonts.googleapis.com/css2?family=Fira+Code:wght@400;500;600&family=Inter:wght@400;500;600;700&display=swap" rel="stylesheet">
</head>
<body class="vscode-dark">
  <header class="app-header">
    <div class="header-left">
      <div class="logo-group">
        <svg class="logo-icon" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
          <path d="M12 2L2 7l10 5 10-5-10-5zM2 17l10 5 10-5M2 12l10 5 10-5"/>
        </svg>
        <div class="title-group">
          <h1>Smart Error Detection System <span class="badge-tag">SEDS 2.0</span></h1>
          <span class="tagline">Detect. Fix. Run. Automatically. (Single-File Standalone)</span>
        </div>
      </div>
    </div>
    <div class="header-center">
      <div id="statusBar" class="status-pill status-ready">
        <span class="status-dot"></span>
        <span id="statusText">System Ready</span>
      </div>
    </div>
    <div class="header-right">
      <div class="ai-controls">
        <label class="toggle-control" title="Enable AI-powered cloud diagnostics">
          <input type="checkbox" id="aiConsentToggle">
          <span class="slider round"></span>
          <span class="toggle-label">AI Cloud Assist</span>
        </label>
        <select id="aiProviderSelect" class="select-control">
          <option value="auto">Auto (OpenAI / Gemini / Local)</option>
          <option value="openai">OpenAI (GPT-4o-mini)</option>
          <option value="gemini">Google Gemini</option>
          <option value="local">Offline Local Engine</option>
        </select>
      </div>
      <button id="btnHeaderHistory" class="btn btn-secondary btn-sm">
        <svg viewBox="0 0 24 24" width="14" height="14" fill="none" stroke="currentColor" stroke-width="2"><circle cx="12" cy="12" r="10"/><polyline points="12 6 12 12 16 14"/></svg>
        History
      </button>
    </div>
  </header>

  <div class="workspace-container">
    <section class="panel left-panel">
      <div class="panel-header">
        <div class="panel-title">
          <svg viewBox="0 0 24 24" width="16" height="16" fill="none" stroke="currentColor" stroke-width="2"><polyline points="16 18 22 12 16 6"/><polyline points="8 6 2 12 8 18"/></svg>
          Python Code Editor
          <span id="currentFileName" class="file-name-tag">script.py</span>
        </div>
        <div class="editor-quick-info"><span id="cursorPos">Ln 1, Col 1</span></div>
      </div>
      <div class="toolbar">
        <button id="btnRun" class="btn btn-primary" title="Execute Code (Ctrl+Enter)">
          <svg viewBox="0 0 24 24" width="14" height="14" fill="currentColor"><polygon points="5 3 19 12 5 21 5 3"/></svg>
          Run Code
        </button>
        <button id="btnOpenFile" class="btn btn-dark" title="Open File">
          <svg viewBox="0 0 24 24" width="14" height="14" fill="none" stroke="currentColor" stroke-width="2"><path d="M22 19a2 2 0 0 1-2 2H4a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h5l2 3h9a2 2 0 0 1 2 2z"/></svg>
          Open
        </button>
        <input type="file" id="fileInput" accept=".py,.txt" style="display: none;">
        <button id="btnSaveFile" class="btn btn-dark" title="Save File">
          <svg viewBox="0 0 24 24" width="14" height="14" fill="none" stroke="currentColor" stroke-width="2"><path d="M19 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h11l5 5v11a2 2 0 0 1-2 2z"/><polyline points="17 21 17 13 7 13 7 21"/><polyline points="7 3 7 8 15 8"/></svg>
          Save
        </button>
        <button id="btnClear" class="btn btn-dark" title="Clear Editor">
          <svg viewBox="0 0 24 24" width="14" height="14" fill="none" stroke="currentColor" stroke-width="2"><polyline points="3 6 5 6 21 6"/><path d="M19 6v14a2 2 0 0 1-2 2H7a2 2 0 0 1-2-2V6m3 0V4a2 2 0 0 1 2-2h4a2 2 0 0 1 2 2v2"/></svg>
          Clear
        </button>
        <button id="btnScanProject" class="btn btn-purple" title="Scan Directory">
          <svg viewBox="0 0 24 24" width="14" height="14" fill="none" stroke="currentColor" stroke-width="2"><path d="M21 16V8a2 2 0 0 0-1-1.73l-7-4a2 2 0 0 0-2 0l-7 4A2 2 0 0 0 3 8v8a2 2 0 0 0 1 1.73l7 4a2 2 0 0 0 2 0l7-4A2 2 0 0 0 21 16z"/></svg>
          Scan Project
        </button>
        <button id="btnUndoFix" class="btn btn-dark" title="Undo Fix" disabled>
          <svg viewBox="0 0 24 24" width="14" height="14" fill="none" stroke="currentColor" stroke-width="2"><path d="M3 7v6h6"/><path d="M21 17a9 9 0 0 0-9-9 9 9 0 0 0-6 2.3L3 13"/></svg>
          Undo Fix
        </button>
      </div>
      <div class="editor-wrapper">
        <div id="lineNumbers" class="line-numbers">1</div>
        <textarea id="codeEditor" spellcheck="false">numbers = [10, 20, 30
print(numbers)</textarea>
      </div>
      <div class="editor-footer">
        <span id="footerLines">2 lines</span>
        <span>Python 3.13</span>
        <span>UTF-8</span>
        <span>Spaces: 4</span>
      </div>
    </section>

    <section class="panel right-panel">
      <div class="panel-section explanation-section">
        <div class="panel-header">
          <div class="panel-title">
            <svg viewBox="0 0 24 24" width="16" height="16" fill="none" stroke="currentColor" stroke-width="2"><circle cx="12" cy="12" r="10"/><line x1="12" y1="8" x2="12" y2="12"/><line x1="12" y1="16" x2="12.01" y2="16"/></svg>
            AI Error Explanation
          </div>
          <div class="error-badges">
            <span id="badgeErrorType" class="badge badge-error">SyntaxError</span>
            <span id="badgeLine" class="badge badge-neutral">Line 1</span>
            <span id="badgeCol" class="badge badge-neutral">Col 22</span>
            <span id="badgeProvider" class="badge badge-provider">Local Engine</span>
          </div>
        </div>
        <div id="explanationContainer" class="explanation-card">
          <div class="expl-item"><div class="expl-label">1. What is the error?</div><div id="explWhat" class="expl-value">Missing closing square bracket ']' on line 1.</div></div>
          <div class="expl-item"><div class="expl-label">2. Where did it start?</div><div id="explWhere" class="expl-value">Line 1, Column 11.</div></div>
          <div class="expl-item"><div class="expl-label">3. Why did it happen?</div><div id="explWhy" class="expl-value">Python requires every opened delimiter to be matched and closed.</div></div>
          <div class="expl-item"><div class="expl-label">4. Root Cause Analysis</div><div id="explCause" class="expl-value">The list declaration on line 1 was not closed before the line break.</div></div>
          <div class="expl-item"><div class="expl-label">5. Affected Code</div><div id="explAffected" class="expl-value code-snippet">numbers = [10, 20, 30</div></div>
          <div class="expl-item"><div class="expl-label">6. How to fix it</div><div id="explHow" class="expl-value">Append a closing square bracket ']' at the end of line 1.</div></div>
        </div>
      </div>

      <div class="panel-section fix-section">
        <div class="panel-header">
          <div class="panel-title">
            <svg viewBox="0 0 24 24" width="16" height="16" fill="none" stroke="currentColor" stroke-width="2"><path d="M14.7 6.3a1 1 0 0 0 0 1.4l1.6 1.6a1 1 0 0 0 1.4 0l3.77-3.77a6 6 0 0 1-7.94 7.94l-6.91 6.91a2.12 2.12 0 0 1-3-3l6.91-6.91a6 6 0 0 1 7.94-7.94l-3.76 3.76z"/></svg>
            AI Suggested Fix & Code Diff
          </div>
          <div class="fix-actions">
            <button id="btnApplyFix" class="btn btn-success btn-sm">Apply Fix</button>
            <button id="btnApplyAndRun" class="btn btn-accent btn-sm">Apply and Run</button>
          </div>
        </div>
        <div class="diff-view-container">
          <div class="diff-tabs">
            <button class="diff-tab active" data-tab="preview">Fixed Code Preview</button>
            <button class="diff-tab" data-tab="unified">Unified Diff</button>
          </div>
          <div id="fixPreviewTab" class="diff-tab-content active"><pre id="fixedCodeDisplay" class="code-block">numbers = [10, 20, 30]\nprint(numbers)</pre></div>
          <div id="fixDiffTab" class="diff-tab-content"><pre id="unifiedDiffDisplay" class="code-block diff-block">--- Original Code\n+++ Suggested Fix\n@@ -1,2 +1,2 @@\n-numbers = [10, 20, 30\n+numbers = [10, 20, 30]\n print(numbers)</pre></div>
        </div>
        <div id="fixNotice" class="fix-validation-notice">
          <span class="notice-icon">✓</span>
          <span id="fixNoticeText">Candidate fix passed AST compilation and syntax validation.</span>
        </div>
      </div>
    </section>
  </div>

  <section class="bottom-panel">
    <div class="tab-bar">
      <button class="tab-btn active" data-bottom-tab="terminal">Terminal Output</button>
      <button class="tab-btn" data-bottom-tab="diagnostics">Execution Status & Sandbox</button>
      <button class="tab-btn" data-bottom-tab="scanner">Project Scan Report <span id="scannerCountBadge" class="tab-badge" style="display: none;">0</span></button>
      <button class="tab-btn" data-bottom-tab="history">Session History & Analytics</button>
      <div class="bottom-panel-stats"><span id="bottomExecTime">Time: -- ms</span><span id="bottomExitCode">Exit: --</span></div>
    </div>
    <div class="tab-content-area">
      <div id="tabTerminal" class="bottom-tab-content active"><div id="terminalOutput" class="terminal-view"><div class="terminal-line system-line">[SEDS Standalone] Ready. Click 'Run Code' or press Ctrl+Enter.</div></div></div>
      <div id="tabDiagnostics" class="bottom-tab-content">
        <div class="diagnostics-grid">
          <div class="diag-card"><h4>Sandbox Architecture</h4><p><strong>Mode:</strong> Restricted Subprocess</p><p><strong>Environment:</strong> Scrubbed Secrets</p><p><strong>Watchdog:</strong> 5.0 seconds</p></div>
          <div class="diag-card"><h4>Process Status</h4><p>Exit: <span id="diagExitCode">0</span></p><p>Duration: <span id="diagDuration">0 ms</span></p></div>
          <div class="diag-card"><h4>Security Disclosures</h4><p class="security-text" id="diagNotice">Disposable temp directory isolation per execution.</p></div>
        </div>
      </div>
      <div id="tabScanner" class="bottom-tab-content">
        <div class="scanner-controls">
          <input type="text" id="scanFolderInput" class="input-control" placeholder="Enter full directory path...">
          <button id="btnStartScan" class="btn btn-purple">Scan Folder</button>
        </div>
        <div id="scanSummaryBar" class="scan-summary-bar" style="display: none;">
          <div class="scan-stat-card">Total: <strong id="scanTotalFiles">0</strong></div>
          <div class="scan-stat-card stat-success">Passed: <strong id="scanPassedFiles">0</strong></div>
          <div class="scan-stat-card stat-error">Failed: <strong id="scanFailedFiles">0</strong></div>
          <div class="scan-stat-card">Duration: <strong id="scanDuration">0 ms</strong></div>
        </div>
        <div id="scanResultsList" class="scan-results-list"><div class="empty-state">No scan run yet.</div></div>
      </div>
      <div id="tabHistory" class="bottom-tab-content">
        <div class="history-grid">
          <div class="history-list-section"><h4>Recent Sessions</h4><div id="sessionsList" class="history-list"></div></div>
          <div class="analytics-section"><h4>Analytics</h4><div id="analyticsStats" class="analytics-card"><p>Total Sessions: <strong id="statTotalSessions">0</strong></p><p>Errors Logged: <strong id="statTotalErrors">0</strong></p><p>Fix Rate: <strong id="statFixRate">0%</strong></p><ul id="statTopErrorsList" class="top-errors-list"></ul></div></div>
        </div>
      </div>
    </div>
  </section>

  <div id="modalScan" class="modal-overlay" style="display: none;">
    <div class="modal-content">
      <div class="modal-header"><h3>Scan Project</h3><button id="btnCloseModal" class="btn-close">&times;</button></div>
      <div class="modal-body"><input type="text" id="modalScanInput" class="input-control modal-input" placeholder="C:\\Path\\To\\Python\\Project"></div>
      <div class="modal-footer"><button id="btnModalCancel" class="btn btn-secondary">Cancel</button><button id="btnModalRunScan" class="btn btn-purple">Run Scan</button></div>
    </div>
  </div>

  <script src="/script.js"></script>
</body>
</html>
"""

CSS_STYLES = """
:root {
  --bg-dark: #1e1e1e; --bg-editor: #181818; --panel-bg: #252526; --header-bg: #141414;
  --border-color: #383838; --text-primary: #cccccc; --text-bright: #ffffff; --text-muted: #858585;
  --text-code: #d4d4d4; --accent-blue: #0e639c; --accent-blue-hover: #1177bb; --success-green: #16a34a;
  --success-green-hover: #22c55e; --danger-red: #ef4444; --purple-accent: #7c3aed;
  --purple-accent-hover: #8b5cf6; --terminal-bg: #0c0c0c; --terminal-fg: #00ff66;
  --font-ui: 'Inter', -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
  --font-code: 'Fira Code', 'Consolas', 'Courier New', monospace;
}
* { box-sizing: border-box; margin: 0; padding: 0; }
body { font-family: var(--font-ui); background-color: var(--bg-dark); color: var(--text-primary); height: 100vh; display: flex; flex-direction: column; overflow: hidden; user-select: none; }
.app-header { height: 50px; background-color: var(--header-bg); border-bottom: 1px solid var(--border-color); display: flex; align-items: center; justify-content: space-between; padding: 0 16px; flex-shrink: 0; }
.header-left .logo-group { display: flex; align-items: center; gap: 10px; }
.logo-icon { width: 24px; height: 24px; color: #38bdf8; }
.title-group h1 { font-size: 14px; font-weight: 700; color: var(--text-bright); display: flex; align-items: center; gap: 8px; }
.badge-tag { font-size: 10px; background-color: #3b82f6; color: #ffffff; padding: 2px 6px; border-radius: 4px; font-weight: 600; }
.tagline { font-size: 11px; color: var(--text-muted); }
.status-pill { display: flex; align-items: center; gap: 8px; font-size: 12px; font-weight: 500; padding: 4px 12px; border-radius: 12px; background-color: rgba(255, 255, 255, 0.05); border: 1px solid var(--border-color); }
.status-dot { width: 8px; height: 8px; border-radius: 50%; background-color: var(--success-green); }
.status-pill.status-ready .status-dot { background-color: var(--success-green); }
.status-pill.status-running .status-dot { background-color: #38bdf8; animation: pulse 1s infinite; }
.status-pill.status-error .status-dot { background-color: var(--danger-red); }
@keyframes pulse { 0%, 100% { opacity: 1; transform: scale(1); } 50% { opacity: 0.4; transform: scale(1.2); } }
.header-right { display: flex; align-items: center; gap: 14px; }
.ai-controls { display: flex; align-items: center; gap: 10px; background-color: rgba(255, 255, 255, 0.03); padding: 3px 8px; border-radius: 6px; border: 1px solid var(--border-color); }
.toggle-control { display: inline-flex; align-items: center; gap: 8px; cursor: pointer; font-size: 12px; color: var(--text-bright); }
.toggle-control input { opacity: 0; width: 0; height: 0; }
.slider { position: relative; width: 28px; height: 16px; background-color: #4b5563; border-radius: 16px; transition: 0.2s; }
.slider:before { position: absolute; content: ""; height: 12px; width: 12px; left: 2px; bottom: 2px; background-color: white; border-radius: 50%; transition: 0.2s; }
input:checked + .slider { background-color: var(--purple-accent); }
input:checked + .slider:before { transform: translateX(12px); }
.select-control { background-color: #2d2d2d; color: var(--text-bright); border: 1px solid var(--border-color); border-radius: 4px; padding: 3px 8px; font-size: 11px; outline: none; }
.btn { display: inline-flex; align-items: center; gap: 6px; padding: 6px 12px; border-radius: 4px; border: 1px solid transparent; font-size: 12px; font-weight: 500; cursor: pointer; outline: none; font-family: var(--font-ui); }
.btn-sm { padding: 4px 8px; font-size: 11px; }
.btn-primary { background-color: var(--accent-blue); color: white; }
.btn-primary:hover { background-color: var(--accent-blue-hover); }
.btn-dark { background-color: #333333; color: var(--text-bright); }
.btn-dark:hover { background-color: #444444; }
.btn-purple { background-color: var(--purple-accent); color: white; }
.btn-purple:hover { background-color: var(--purple-accent-hover); }
.btn-success { background-color: var(--success-green); color: white; }
.btn-success:hover { background-color: var(--success-green-hover); }
.btn-accent { background: linear-gradient(135deg, #16a34a, #0e639c); color: white; }
.btn:disabled { opacity: 0.4; cursor: not-allowed; }
.workspace-container { display: grid; grid-template-columns: 1fr 1fr; flex: 1; min-height: 0; background-color: var(--bg-dark); }
.panel { display: flex; flex-direction: column; min-height: 0; overflow: hidden; }
.left-panel { border-right: 1px solid var(--border-color); }
.panel-header { height: 38px; background-color: var(--panel-bg); border-bottom: 1px solid var(--border-color); display: flex; align-items: center; justify-content: space-between; padding: 0 12px; flex-shrink: 0; }
.panel-title { font-size: 12px; font-weight: 600; color: var(--text-bright); display: flex; align-items: center; gap: 8px; text-transform: uppercase; letter-spacing: 0.5px; }
.file-name-tag { text-transform: none; font-weight: 400; color: #9cdcfe; background-color: rgba(156, 220, 254, 0.1); padding: 2px 6px; border-radius: 3px; font-size: 11px; }
.toolbar { height: 42px; background-color: #1f1f1f; border-bottom: 1px solid var(--border-color); display: flex; align-items: center; gap: 8px; padding: 0 10px; flex-shrink: 0; }
.editor-wrapper { display: flex; flex: 1; min-height: 0; background-color: var(--bg-editor); overflow: hidden; }
.line-numbers { width: 44px; background-color: #1e1e1e; border-right: 1px solid #2d2d2d; color: var(--text-muted); font-family: var(--font-code); font-size: 13px; line-height: 20px; text-align: right; padding: 10px 8px 10px 0; overflow: hidden; white-space: pre-wrap; }
.line-numbers .error-marker { color: #ff5555 !important; font-weight: 700; background: rgba(255, 85, 85, 0.22); border-left: 3px solid #ff5555; padding-left: 2px; display: block; }
#codeEditor { flex: 1; background-color: var(--bg-editor); color: var(--text-code); font-family: var(--font-code); font-size: 13px; line-height: 20px; padding: 10px; border: none; outline: none; resize: none; white-space: pre; overflow: auto; tab-size: 4; }
.editor-footer { height: 24px; background-color: #141414; border-top: 1px solid var(--border-color); display: flex; align-items: center; justify-content: flex-end; gap: 16px; padding: 0 12px; font-size: 11px; color: var(--text-muted); }
.right-panel { display: flex; flex-direction: column; background-color: var(--bg-dark); }
.panel-section { display: flex; flex-direction: column; flex: 1; min-height: 0; }
.explanation-section { border-bottom: 1px solid var(--border-color); }
.error-badges { display: flex; align-items: center; gap: 6px; }
.badge { font-size: 11px; padding: 2px 8px; border-radius: 4px; font-weight: 600; }
.badge-error { background-color: rgba(239, 68, 68, 0.2); color: #f87171; border: 1px solid rgba(239, 68, 68, 0.4); }
.badge-neutral { background-color: #333333; color: #e5e5e5; }
.badge-provider { background-color: rgba(124, 58, 237, 0.2); color: #c084fc; border: 1px solid rgba(124, 58, 237, 0.4); }
.explanation-card { flex: 1; overflow-y: auto; padding: 12px; display: flex; flex-direction: column; gap: 10px; background-color: #1e1e1e; }
.expl-item { background-color: #252526; border: 1px solid #333333; border-radius: 6px; padding: 8px 12px; }
.expl-label { font-size: 11px; font-weight: 700; color: #60a5fa; margin-bottom: 4px; text-transform: uppercase; }
.expl-value { font-size: 12px; color: #e2e8f0; line-height: 18px; }
.expl-value.code-snippet { font-family: var(--font-code); background-color: #181818; padding: 4px 8px; border-radius: 4px; border-left: 3px solid var(--danger-red); }
.fix-actions { display: flex; gap: 8px; }
.diff-view-container { flex: 1; display: flex; flex-direction: column; min-height: 0; padding: 8px 12px; }
.diff-tabs { display: flex; gap: 4px; margin-bottom: 6px; }
.diff-tab { background-color: #2b2b2b; border: 1px solid var(--border-color); color: var(--text-muted); font-size: 11px; padding: 4px 10px; border-radius: 4px 4px 0 0; cursor: pointer; }
.diff-tab.active { background-color: #181818; color: var(--text-bright); border-bottom-color: transparent; }
.diff-tab-content { display: none; flex: 1; min-height: 0; overflow: auto; background-color: #181818; border: 1px solid var(--border-color); border-radius: 0 4px 4px 4px; padding: 8px; }
.diff-tab-content.active { display: block; }
.code-block { font-family: var(--font-code); font-size: 12px; line-height: 18px; color: #ce9178; white-space: pre; }
.diff-block { color: #d4d4d4; }
.fix-validation-notice { display: flex; align-items: center; gap: 8px; background-color: rgba(22, 163, 74, 0.15); border-top: 1px solid rgba(22, 163, 74, 0.3); padding: 6px 12px; font-size: 11px; color: #4ade80; }
.bottom-panel { height: 250px; background-color: var(--header-bg); border-top: 1px solid var(--border-color); display: flex; flex-direction: column; flex-shrink: 0; }
.tab-bar { height: 36px; background-color: #1f1f1f; border-bottom: 1px solid var(--border-color); display: flex; align-items: center; padding: 0 10px; gap: 4px; }
.tab-btn { background: transparent; border: none; color: var(--text-muted); font-size: 12px; display: inline-flex; align-items: center; gap: 6px; padding: 6px 12px; cursor: pointer; }
.tab-btn.active { color: var(--text-bright); background-color: var(--terminal-bg); border-bottom: 2px solid #38bdf8; }
.tab-badge { background-color: var(--danger-red); color: white; font-size: 10px; border-radius: 10px; padding: 1px 6px; }
.bottom-panel-stats { margin-left: auto; display: flex; gap: 12px; font-size: 11px; color: var(--text-muted); }
.tab-content-area { flex: 1; min-height: 0; overflow: hidden; background-color: var(--terminal-bg); }
.bottom-tab-content { display: none; height: 100%; overflow-y: auto; padding: 10px 14px; }
.bottom-tab-content.active { display: block; }
.terminal-view { font-family: var(--font-code); font-size: 12px; line-height: 18px; color: var(--terminal-fg); white-space: pre-wrap; word-break: break-all; }
.terminal-line.error-line { color: #ff6b6b; }
.terminal-line.system-line { color: #38bdf8; }
.diagnostics-grid { display: grid; grid-template-columns: repeat(3, 1fr); gap: 12px; }
.diag-card { background-color: #1e1e1e; border: 1px solid #333333; border-radius: 6px; padding: 12px; font-size: 12px; line-height: 20px; }
.diag-card h4 { color: #60a5fa; font-size: 13px; margin-bottom: 8px; }
.security-text { color: #fbbf24; }
.scanner-controls { display: flex; gap: 10px; margin-bottom: 12px; }
.input-control { flex: 1; background-color: #1e1e1e; border: 1px solid var(--border-color); border-radius: 4px; color: var(--text-bright); padding: 6px 10px; font-size: 12px; outline: none; }
.scan-summary-bar { display: flex; gap: 12px; margin-bottom: 12px; }
.scan-stat-card { background-color: #1e1e1e; border: 1px solid #333333; padding: 6px 12px; border-radius: 4px; font-size: 12px; }
.scan-stat-card.stat-success strong { color: #4ade80; }
.scan-stat-card.stat-error strong { color: #f87171; }
.scan-results-list { display: flex; flex-direction: column; gap: 8px; }
.scan-file-card { background-color: #1e1e1e; border: 1px solid #333; border-radius: 4px; padding: 8px 12px; }
.scan-file-card.has-error { border-left: 4px solid var(--danger-red); }
.scan-file-card.passed { border-left: 4px solid var(--success-green); }
.history-grid { display: grid; grid-template-columns: 2fr 1fr; gap: 14px; }
.history-list { display: flex; flex-direction: column; gap: 6px; max-height: 180px; overflow-y: auto; }
.history-item { background-color: #1e1e1e; border: 1px solid #333; padding: 6px 10px; border-radius: 4px; font-size: 11px; display: flex; justify-content: space-between; cursor: pointer; }
.analytics-card { background-color: #1e1e1e; border: 1px solid #333; border-radius: 6px; padding: 10px 14px; font-size: 12px; line-height: 22px; }
.top-errors-list { padding-left: 18px; color: #f87171; }
.empty-state { color: var(--text-muted); font-size: 12px; font-style: italic; padding: 12px 0; }
.modal-overlay { position: fixed; inset: 0; background-color: rgba(0, 0, 0, 0.6); display: flex; align-items: center; justify-content: center; z-index: 1000; }
.modal-content { background-color: #252526; border: 1px solid var(--border-color); border-radius: 6px; width: 480px; }
.modal-header { padding: 12px 16px; border-bottom: 1px solid var(--border-color); display: flex; justify-content: space-between; align-items: center; }
.modal-header h3 { font-size: 14px; color: var(--text-bright); }
.btn-close { background: transparent; border: none; color: var(--text-muted); font-size: 18px; cursor: pointer; }
.modal-body { padding: 16px; }
.modal-footer { padding: 10px 16px; border-top: 1px solid var(--border-color); display: flex; justify-content: flex-end; gap: 8px; }
::-webkit-scrollbar { width: 8px; height: 8px; }
::-webkit-scrollbar-thumb { background: #3a3a3a; border-radius: 4px; }
"""

JS_SCRIPT = """
document.addEventListener("DOMContentLoaded", () => {
  const codeEditor = document.getElementById("codeEditor");
  const lineNumbers = document.getElementById("lineNumbers");
  const cursorPos = document.getElementById("cursorPos");
  const footerLines = document.getElementById("footerLines");
  const currentFileName = document.getElementById("currentFileName");
  const statusBar = document.getElementById("statusBar");
  const statusText = document.getElementById("statusText");

  const aiConsentToggle = document.getElementById("aiConsentToggle");
  const aiProviderSelect = document.getElementById("aiProviderSelect");

  const btnRun = document.getElementById("btnRun");
  const btnOpenFile = document.getElementById("btnOpenFile");
  const fileInput = document.getElementById("fileInput");
  const btnSaveFile = document.getElementById("btnSaveFile");
  const btnClear = document.getElementById("btnClear");
  const btnScanProject = document.getElementById("btnScanProject");
  const btnUndoFix = document.getElementById("btnUndoFix");

  const badgeErrorType = document.getElementById("badgeErrorType");
  const badgeLine = document.getElementById("badgeLine");
  const badgeCol = document.getElementById("badgeCol");
  const badgeProvider = document.getElementById("badgeProvider");
  const explWhat = document.getElementById("explWhat");
  const explWhere = document.getElementById("explWhere");
  const explWhy = document.getElementById("explWhy");
  const explCause = document.getElementById("explCause");
  const explAffected = document.getElementById("explAffected");
  const explHow = document.getElementById("explHow");

  const fixedCodeDisplay = document.getElementById("fixedCodeDisplay");
  const unifiedDiffDisplay = document.getElementById("unifiedDiffDisplay");
  const fixNotice = document.getElementById("fixNotice");
  const fixNoticeText = document.getElementById("fixNoticeText");
  const btnApplyFix = document.getElementById("btnApplyFix");
  const btnApplyAndRun = document.getElementById("btnApplyAndRun");

  const terminalOutput = document.getElementById("terminalOutput");
  const bottomExecTime = document.getElementById("bottomExecTime");
  const bottomExitCode = document.getElementById("bottomExitCode");
  const diagExitCode = document.getElementById("diagExitCode");
  const diagDuration = document.getElementById("diagDuration");
  const diagNotice = document.getElementById("diagNotice");

  const scanFolderInput = document.getElementById("scanFolderInput");
  const btnStartScan = document.getElementById("btnStartScan");
  const scanSummaryBar = document.getElementById("scanSummaryBar");
  const scanTotalFiles = document.getElementById("scanTotalFiles");
  const scanPassedFiles = document.getElementById("scanPassedFiles");
  const scanFailedFiles = document.getElementById("scanFailedFiles");
  const scanDuration = document.getElementById("scanDuration");
  const scanResultsList = document.getElementById("scanResultsList");
  const scannerCountBadge = document.getElementById("scannerCountBadge");

  const btnHeaderHistory = document.getElementById("btnHeaderHistory");
  const sessionsList = document.getElementById("sessionsList");
  const statTotalSessions = document.getElementById("statTotalSessions");
  const statTotalErrors = document.getElementById("statTotalErrors");
  const statFixRate = document.getElementById("statFixRate");
  const statTopErrorsList = document.getElementById("statTopErrorsList");

  const modalScan = document.getElementById("modalScan");
  const modalScanInput = document.getElementById("modalScanInput");
  const btnCloseModal = document.getElementById("btnCloseModal");
  const btnModalCancel = document.getElementById("btnModalCancel");
  const btnModalRunScan = document.getElementById("btnModalRunScan");

  let undoStack = [];
  let currentSuggestedFix = null;
  let activeErrorLine = null;

  function updateLineNumbers(highlightLine = null) {
    const lines = codeEditor.value.split("\\n");
    const count = lines.length;
    let html = "";
    for (let i = 1; i <= count; i++) {
      if (highlightLine && i === highlightLine) {
        html += `<span class="error-marker">&gt; ${i}</span>\\n`;
      } else {
        html += `${i}\\n`;
      }
    }
    lineNumbers.innerHTML = html;
    footerLines.textContent = `${count} line${count > 1 ? "s" : ""}`;
  }

  function updateCursorPosition() {
    const text = codeEditor.value.substring(0, codeEditor.selectionStart);
    const lines = text.split("\\n");
    cursorPos.textContent = `Ln ${lines.length}, Col ${lines[lines.length - 1].length + 1}`;
  }

  function highlightAndScrollToLine(lineNumber) {
    if (!lineNumber || lineNumber < 1) return;
    const lines = codeEditor.value.split("\\n");
    let charOffset = 0;
    for (let i = 0; i < lineNumber - 1 && i < lines.length; i++) {
      charOffset += lines[i].length + 1;
    }
    const lineEnd = charOffset + (lines[lineNumber - 1] ? lines[lineNumber - 1].length : 0);
    codeEditor.focus();
    codeEditor.setSelectionRange(charOffset, lineEnd);
    codeEditor.scrollTop = Math.max(0, (lineNumber - 3) * 20);
    lineNumbers.scrollTop = codeEditor.scrollTop;
  }

  codeEditor.addEventListener("input", () => { updateLineNumbers(activeErrorLine); updateCursorPosition(); });
  codeEditor.addEventListener("keyup", updateCursorPosition);
  codeEditor.addEventListener("click", updateCursorPosition);
  codeEditor.addEventListener("scroll", () => { lineNumbers.scrollTop = codeEditor.scrollTop; });

  codeEditor.addEventListener("keydown", (e) => {
    if (e.key === "Tab") {
      e.preventDefault();
      const start = codeEditor.selectionStart;
      codeEditor.value = codeEditor.value.substring(0, start) + "    " + codeEditor.value.substring(codeEditor.selectionEnd);
      codeEditor.selectionStart = codeEditor.selectionEnd = start + 4;
      updateLineNumbers();
    } else if (e.ctrlKey && e.key === "Enter") {
      e.preventDefault();
      runCode();
    }
  });

  function setStatus(text, type = "ready") {
    statusText.textContent = text;
    statusBar.className = `status-pill status-${type}`;
  }

  function logTerminal(text, type = "normal") {
    const line = document.createElement("div");
    line.className = `terminal-line ${type === "error" ? "error-line" : type === "system" ? "system-line" : ""}`;
    line.textContent = text;
    terminalOutput.appendChild(line);
    terminalOutput.scrollTop = terminalOutput.scrollHeight;
  }

  async function runCode() {
    const code = codeEditor.value;
    if (!code.trim()) return setStatus("Editor empty", "ready");

    setStatus("Executing in Sandbox...", "running");
    terminalOutput.innerHTML = "";
    logTerminal(`[SEDS Runner] Executing code...`, "system");

    const payload = {
      code: code,
      user_consent: aiConsentToggle.checked,
      preferred_provider: aiProviderSelect.value,
    };

    try {
      const resp = await fetch("/api/run", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify(payload),
      });
      const data = await resp.json();

      bottomExecTime.textContent = `Time: ${data.duration_ms} ms`;
      bottomExitCode.textContent = `Exit: ${data.exit_code}`;
      diagExitCode.textContent = data.exit_code;
      diagDuration.textContent = `${data.duration_ms} ms`;
      if (data.security_notice) diagNotice.textContent = data.security_notice;

      if (data.stdout) logTerminal(data.stdout);
      if (data.stderr) logTerminal(data.stderr, "error");

      if (data.exit_code === 0 && (!data.errors || data.errors.length === 0)) {
        setStatus("Success", "ready");
        activeErrorLine = null;
        updateLineNumbers();
        badgeErrorType.textContent = "No Errors";
        badgeErrorType.className = "badge badge-neutral";
        badgeLine.textContent = "Clean";
        badgeCol.textContent = "--";
        explWhat.textContent = "No errors detected!";
        explWhere.textContent = "Clean execution.";
        explWhy.textContent = "Code is syntactically and semantically sound.";
        explCause.textContent = "None";
        explAffected.textContent = "None";
        explHow.textContent = "Program ran smoothly.";
        currentSuggestedFix = null;
        btnApplyFix.disabled = true;
        btnApplyAndRun.disabled = true;
        fixedCodeDisplay.textContent = "No fix required.";
        unifiedDiffDisplay.textContent = "No diff.";
      } else {
        const primary = data.primary_error || (data.errors && data.errors[0]);
        if (primary) {
          setStatus(`Error: ${primary.error_type}`, "error");
          activeErrorLine = primary.line;
          updateLineNumbers(activeErrorLine);
          highlightAndScrollToLine(primary.line);

          badgeErrorType.textContent = primary.error_type;
          badgeErrorType.className = "badge badge-error";
          badgeLine.textContent = `Line ${primary.line}`;
          badgeCol.textContent = `Col ${primary.column || 1}`;

          if (data.explanation) {
            badgeProvider.textContent = data.explanation.provider === "ai" ? "Cloud AI" : "Local Engine";
            explWhat.textContent = data.explanation.what || primary.message;
            explWhere.textContent = data.explanation.where || `Line ${primary.line}`;
            explWhy.textContent = data.explanation.why || "";
            explCause.textContent = data.explanation.cause || primary.message;
            explAffected.textContent = data.explanation.affected || primary.source_snippet;
            explHow.textContent = data.explanation.how_to_fix || "";
          }

          if (data.fix && data.fix.fixed_code) {
            currentSuggestedFix = data.fix.fixed_code;
            fixedCodeDisplay.textContent = currentSuggestedFix;
            unifiedDiffDisplay.textContent = data.fix.diff || "No diff available.";
            btnApplyFix.disabled = false;
            btnApplyAndRun.disabled = false;
            fixNotice.style.display = "flex";
            fixNoticeText.textContent = data.fix.validation_notes || "Passed AST validation.";
          } else {
            currentSuggestedFix = null;
            btnApplyFix.disabled = true;
            btnApplyAndRun.disabled = true;
            fixedCodeDisplay.textContent = "No automatic fix inferred.";
            unifiedDiffDisplay.textContent = "No diff.";
            fixNotice.style.display = "none";
          }
        }
      }
    } catch (err) {
      setStatus("Server Error", "error");
      logTerminal(`[SEDS Error] ${err.message}`, "error");
    }
  }

  function applyFix() {
    if (!currentSuggestedFix) return;
    undoStack.push(codeEditor.value);
    btnUndoFix.disabled = false;
    codeEditor.value = currentSuggestedFix;
    updateLineNumbers();
    setStatus("Fix applied", "ready");
    logTerminal("[SEDS] Candidate fix applied.", "system");
  }

  btnApplyFix.addEventListener("click", applyFix);
  btnApplyAndRun.addEventListener("click", async () => { applyFix(); await runCode(); });

  btnUndoFix.addEventListener("click", () => {
    if (undoStack.length > 0) {
      codeEditor.value = undoStack.pop();
      updateLineNumbers();
      btnUndoFix.disabled = undoStack.length === 0;
      setStatus("Fix undone", "ready");
    }
  });

  btnOpenFile.addEventListener("click", () => fileInput.click());
  fileInput.addEventListener("change", (e) => {
    const file = e.target.files[0];
    if (file) {
      const reader = new FileReader();
      reader.onload = (event) => {
        codeEditor.value = event.target.result;
        currentFileName.textContent = file.name;
        updateLineNumbers();
        setStatus(`Loaded ${file.name}`, "ready");
      };
      reader.readAsText(file);
    }
  });

  btnSaveFile.addEventListener("click", () => {
    const blob = new Blob([codeEditor.value], { type: "text/x-python;charset=utf-8" });
    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = currentFileName.textContent || "script.py";
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    URL.revokeObjectURL(url);
  });

  btnClear.addEventListener("click", () => {
    if (confirm("Clear editor?")) {
      undoStack.push(codeEditor.value);
      btnUndoFix.disabled = false;
      codeEditor.value = "";
      updateLineNumbers();
      setStatus("Cleared", "ready");
    }
  });

  btnRun.addEventListener("click", runCode);

  document.querySelectorAll(".diff-tab").forEach((tab) => {
    tab.addEventListener("click", () => {
      document.querySelectorAll(".diff-tab").forEach((t) => t.classList.remove("active"));
      document.querySelectorAll(".diff-tab-content").forEach((c) => c.classList.remove("active"));
      tab.classList.add("active");
      const target = tab.getAttribute("data-tab");
      document.getElementById(target === "preview" ? "fixPreviewTab" : "fixDiffTab").classList.add("active");
    });
  });

  document.querySelectorAll(".tab-btn").forEach((btn) => {
    btn.addEventListener("click", () => {
      document.querySelectorAll(".tab-btn").forEach((b) => b.classList.remove("active"));
      document.querySelectorAll(".bottom-tab-content").forEach((c) => c.classList.remove("active"));
      btn.classList.add("active");
      const tabName = btn.getAttribute("data-bottom-tab");
      const tabMap = { terminal: "tabTerminal", diagnostics: "tabDiagnostics", scanner: "tabScanner", history: "tabHistory" };
      if (tabMap[tabName]) document.getElementById(tabMap[tabName]).classList.add("active");
      if (tabName === "history") fetchHistory();
    });
  });

  btnScanProject.addEventListener("click", () => { modalScan.style.display = "flex"; modalScanInput.focus(); });
  btnCloseModal.addEventListener("click", () => (modalScan.style.display = "none"));
  btnModalCancel.addEventListener("click", () => (modalScan.style.display = "none"));
  btnModalRunScan.addEventListener("click", () => {
    const path = modalScanInput.value.trim();
    if (!path) return;
    modalScan.style.display = "none";
    scanFolderInput.value = path;
    document.querySelector('.tab-btn[data-bottom-tab="scanner"]').click();
    executeScan(path);
  });

  btnStartScan.addEventListener("click", () => {
    const path = scanFolderInput.value.trim();
    if (path) executeScan(path);
  });

  async function executeScan(folderPath) {
    setStatus("Scanning Project...", "running");
    scanResultsList.innerHTML = `<div class="empty-state">Scanning Python files in ${folderPath}...</div>`;
    try {
      const resp = await fetch("/api/scan", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ folder_path: folderPath }),
      });
      const data = await resp.json();
      if (!resp.ok) throw new Error(data.error || "Scan failed");

      const report = data.report;
      scanSummaryBar.style.display = "flex";
      scanTotalFiles.textContent = report.total_files;
      scanPassedFiles.textContent = report.passed_files;
      scanFailedFiles.textContent = report.failed_files;
      scanDuration.textContent = `${report.duration_ms} ms`;
      scannerCountBadge.style.display = report.failed_files > 0 ? "inline-block" : "none";
      scannerCountBadge.textContent = report.failed_files;

      let html = "";
      report.files.forEach((file) => {
        const isErr = file.status === "ERROR";
        html += `
          <div class="scan-file-card ${isErr ? "has-error" : "passed"}">
            <div style="display:flex; justify-content:space-between; font-weight:600; font-size:12px; margin-bottom:4px;">
              <span>${file.relative_path}</span>
              <span style="color: ${isErr ? "#f87171" : "#4ade80"}">${file.status}</span>
            </div>
            <div style="font-size:11px; color:#94a3b8;">${file.file_path}</div>
            ${file.errors && file.errors.length > 0 ? file.errors.map(err => `
              <div style="margin-top:6px; padding:4px 8px; background:#141414; border-radius:4px; font-size:11px; color:#f87171;">
                Line ${err.line}: [${err.error_type}] ${err.message}
              </div>`).join("") : ""}
          </div>`;
      });
      scanResultsList.innerHTML = html;
      setStatus(`Scan complete: ${report.failed_files} error(s)`, report.failed_files > 0 ? "error" : "ready");
    } catch (err) {
      scanResultsList.innerHTML = `<div class="empty-state" style="color:#f87171;">Scan Error: ${err.message}</div>`;
      setStatus("Scan failed", "error");
    }
  }

  async function fetchHistory() {
    try {
      const resp = await fetch("/api/history");
      const data = await resp.json();
      statTotalSessions.textContent = data.analytics.total_sessions || 0;
      statTotalErrors.textContent = data.analytics.total_errors_detected || 0;
      const rate = data.analytics.total_errors_detected > 0
        ? Math.round((data.analytics.fixes_applied / data.analytics.total_errors_detected) * 100) : 0;
      statFixRate.textContent = `${rate}%`;

      statTopErrorsList.innerHTML = "";
      if (data.analytics.top_errors && data.analytics.top_errors.length > 0) {
        data.analytics.top_errors.forEach((e) => {
          const li = document.createElement("li");
          li.textContent = `${e.error_type}: ${e.count} time(s)`;
          statTopErrorsList.appendChild(li);
        });
      }

      sessionsList.innerHTML = "";
      if (data.sessions && data.sessions.length > 0) {
        data.sessions.forEach((s) => {
          const item = document.createElement("div");
          item.className = "history-item";
          item.innerHTML = `<span><strong>${s.title}</strong> (${s.error_type || "Success"})</span><span style="color:#858585;">${s.created_at}</span>`;
          item.addEventListener("click", () => {
            codeEditor.value = s.source_code;
            updateLineNumbers();
            setStatus(`Loaded session #${s.id}`, "ready");
          });
          sessionsList.appendChild(item);
        });
      }
    } catch (e) { console.error("History failed:", e); }
  }

  btnHeaderHistory.addEventListener("click", () => {
    document.querySelector('.tab-btn[data-bottom-tab="history"]').click();
  });

  updateLineNumbers(1);
  updateCursorPosition();
});
"""


# =============================================================================
# 9. FLASK APPLICATION SERVER
# =============================================================================

app = Flask("SEDS_Standalone")
cors_origins_env = os.getenv("CORS_ORIGINS", "*").strip()
if cors_origins_env == "*":
    CORS(app, resources={r"/api/*": {"origins": "*"}, r"/healthz": {"origins": "*"}})
else:
    allowed_list = [origin.strip() for origin in cors_origins_env.split(",") if origin.strip()]
    CORS(app, resources={r"/api/*": {"origins": allowed_list}, r"/healthz": {"origins": allowed_list}})

Database.init_db()


@app.route("/healthz", methods=["GET"])
def api_health():
    return jsonify({"status": "healthy", "service": "SEDS Standalone", "version": "2.0.0"}), 200


@app.route("/")
def serve_index():
    return Response(HTML_PAGE, mimetype="text/html")


@app.route("/style.css")
def serve_css():
    return Response(CSS_STYLES, mimetype="text/css")


@app.route("/script.js")
def serve_js():
    return Response(JS_SCRIPT, mimetype="application/javascript")


@app.route("/api/status", methods=["GET"])
def api_status():
    return jsonify({
        "status": "online",
        "system": "Smart Error Detection System (SEDS) Standalone Edition",
        "version": "2.0.0",
        "ai": AIService.get_status(),
        "sandbox": {
            "timeout_seconds": float(os.getenv("EXECUTION_TIMEOUT_SECONDS", "5.0")),
            "secrets_scrubbed": True,
        },
    })


@app.route("/api/detect", methods=["POST"])
def api_detect():
    data = request.get_json(force=True, silent=True) or {}
    code = data.get("code", "")
    errors = ErrorDetector.detect_static(code)
    error_list = [e.to_dict() for e in errors]

    primary_error = None
    explanation = None
    fix = None

    if errors:
        primary_error = errors[0]
        consent = bool(data.get("user_consent", False))
        provider = data.get("preferred_provider", "auto")
        explanation = ErrorExplainer.explain(primary_error, code, user_consent=consent, preferred_provider=provider).to_dict()
        fix = AutoFixer.generate_fix(primary_error, code, user_consent=consent, preferred_provider=provider).to_dict()

    return jsonify({
        "errors": error_list,
        "count": len(error_list),
        "primary_error": primary_error.to_dict() if primary_error else None,
        "explanation": explanation,
        "fix": fix,
    })


@app.route("/api/run", methods=["POST"])
def api_run():
    data = request.get_json(force=True, silent=True) or {}
    code = data.get("code", "")
    timeout = float(data.get("timeout", os.getenv("EXECUTION_TIMEOUT_SECONDS", "5.0")))
    consent = bool(data.get("user_consent", False))
    provider = data.get("preferred_provider", "auto")

    static_errors = ErrorDetector.detect_static(code)
    if any(e.severity == "error" for e in static_errors):
        primary_err = static_errors[0]
        expl = ErrorExplainer.explain(primary_err, code, user_consent=consent, preferred_provider=provider)
        fix = AutoFixer.generate_fix(primary_err, code, user_consent=consent, preferred_provider=provider)

        session_id = Database.save_session(
            title="Static Error Detected",
            source_code=code,
            error_type=primary_err.error_type,
            error_line=primary_err.line,
            error_message=primary_err.message,
            applied_fix=fix.fixed_code if fix.is_valid else None,
            execution_output=f"Static Syntax Check Failed on Line {primary_err.line}",
        )
        Database.log_error(
            error_type=primary_err.error_type,
            error_message=primary_err.message,
            line=primary_err.line,
            column=primary_err.column,
            source_snippet=primary_err.source_snippet,
            session_id=session_id,
            fixed_successfully=fix.is_valid,
            provider_used=expl.provider,
        )

        return jsonify({
            "stdout": "",
            "stderr": f"Static Error Detected: {primary_err.error_type} on Line {primary_err.line}: {primary_err.message}",
            "exit_code": 1,
            "duration_ms": 0.0,
            "timed_out": False,
            "errors": [e.to_dict() for e in static_errors],
            "primary_error": primary_err.to_dict(),
            "explanation": expl.to_dict(),
            "fix": fix.to_dict(),
            "security_notice": "Static syntax check caught issue prior to execution.",
            "session_id": session_id,
        })

    run_result = CodeRunner.run_code(code, timeout=timeout)
    detected_errors = []
    primary_err = None
    explanation = None
    fix = None

    if run_result.exit_code != 0:
        detected_errors = ErrorDetector.detect_all(code, runtime_stderr=run_result.stderr)
        if detected_errors:
            primary_err = detected_errors[0]
            expl = ErrorExplainer.explain(primary_err, code, user_consent=consent, preferred_provider=provider)
            explanation = expl.to_dict()
            fix_obj = AutoFixer.generate_fix(primary_err, code, user_consent=consent, preferred_provider=provider)
            fix = fix_obj.to_dict()

    session_id = Database.save_session(
        title="Code Execution Run",
        source_code=code,
        error_type=primary_err.error_type if primary_err else None,
        error_line=primary_err.line if primary_err else None,
        error_message=primary_err.message if primary_err else None,
        applied_fix=fix.get("fixed_code") if fix and fix.get("is_valid") else None,
        execution_output=run_result.stdout or run_result.stderr,
    )

    if primary_err:
        Database.log_error(
            error_type=primary_err.error_type,
            error_message=primary_err.message,
            line=primary_err.line,
            column=primary_err.column,
            source_snippet=primary_err.source_snippet,
            session_id=session_id,
            fixed_successfully=fix.get("is_valid", False) if fix else False,
            provider_used=explanation.get("provider", "local") if explanation else "local",
        )

    return jsonify({
        "stdout": run_result.stdout,
        "stderr": run_result.stderr,
        "exit_code": run_result.exit_code,
        "duration_ms": run_result.duration_ms,
        "timed_out": run_result.timed_out,
        "errors": [e.to_dict() for e in detected_errors],
        "primary_error": primary_err.to_dict() if primary_err else None,
        "explanation": explanation,
        "fix": fix,
        "security_notice": run_result.security_notice,
        "session_id": session_id,
    })


@app.route("/api/fix", methods=["POST"])
def api_fix():
    data = request.get_json(force=True, silent=True) or {}
    code = data.get("code", "")
    err_dict = data.get("error", {})
    consent = bool(data.get("user_consent", False))
    provider = data.get("preferred_provider", "auto")

    if not err_dict:
        errs = ErrorDetector.detect_static(code)
        if not errs:
            return jsonify({"error": "No error provided or detected to fix."}), 400
        error_obj = errs[0]
    else:
        error_obj = DetectedError(
            error_type=err_dict.get("error_type", "SyntaxError"),
            message=err_dict.get("message", ""),
            line=err_dict.get("line", 1),
            column=err_dict.get("column", 1),
            source_snippet=err_dict.get("source_snippet", ""),
            category=err_dict.get("category", "syntax"),
            details=err_dict.get("details", {}),
        )

    fix = AutoFixer.generate_fix(error_obj, code, user_consent=consent, preferred_provider=provider)
    return jsonify({"fix": fix.to_dict()})


@app.route("/api/scan", methods=["POST"])
def api_scan():
    data = request.get_json(force=True, silent=True) or {}
    folder_path = data.get("folder_path", "").strip()
    if not folder_path:
        return jsonify({"error": "folder_path is required."}), 400

    try:
        report_data = ProjectScanner.scan_directory(folder_path)
        scan_id = Database.save_scan(
            folder_path=report_data["folder_path"],
            total_files=report_data["total_files"],
            passed_files=report_data["passed_files"],
            failed_files=report_data["failed_files"],
            report_data=report_data,
        )
        report_data["scan_id"] = scan_id
        return jsonify({"report": report_data})
    except ValueError as val_err:
        return jsonify({"error": str(val_err)}), 404
    except Exception as exc:
        return jsonify({"error": f"Scan failed: {exc}"}), 500


@app.route("/api/history", methods=["GET"])
def api_history():
    return jsonify({
        "sessions": Database.get_recent_sessions(limit=25),
        "scans": Database.get_scan_history(limit=10),
        "analytics": Database.get_analytics(),
    })


# =============================================================================
# 10. OPTIONAL TKINTER DESKTOP MODE
# =============================================================================

def run_tkinter_gui():
    """Native Tkinter desktop window mode (like original SEDS_fixed.py, upgraded)."""
    import tkinter as tk
    from tkinter import filedialog, messagebox, scrolledtext

    root = tk.Tk()
    root.title("Smart Error Detection System (SEDS) - Desktop Mode")
    root.geometry("1280x800")
    root.configure(bg="#1e1e1e")

    # Build Tkinter UI
    top = tk.Frame(root, bg="#1e1e1e")
    top.pack(fill=tk.X, padx=8, pady=8)
    tk.Label(top, text="Smart Error Detection System", bg="#1e1e1e", fg="white", font=("Arial", 14, "bold")).pack(side=tk.LEFT)
    status_lbl = tk.Label(top, text="Ready", bg="#1e1e1e", fg="#9cdcfe", font=("Arial", 11))
    status_lbl.pack(side=tk.RIGHT)

    panes = tk.PanedWindow(root, orient=tk.HORIZONTAL, bg="#1e1e1e", sashwidth=6)
    panes.pack(fill=tk.BOTH, expand=True, padx=8, pady=4)

    left = tk.Frame(panes, bg="#1e1e1e")
    right = tk.Frame(panes, bg="#1e1e1e")
    panes.add(left, width=650)
    panes.add(right, width=600)

    tk.Label(left, text="Python Code Editor", bg="#1e1e1e", fg="white", font=("Arial", 11, "bold")).pack(anchor="w")
    editor = scrolledtext.ScrolledText(left, wrap=tk.NONE, bg="#101010", fg="#d4d4d4", insertbackground="white", font=("Consolas", 11), undo=True)
    editor.pack(fill=tk.BOTH, expand=True, pady=4)
    editor.insert("1.0", "numbers = [10, 20, 30\\nprint(numbers)\\n")

    tk.Label(right, text="AI Error Explanation (7 Dimensions)", bg="#1e1e1e", fg="white", font=("Arial", 11, "bold")).pack(anchor="w")
    expl_box = scrolledtext.ScrolledText(right, height=10, wrap=tk.WORD, bg="#252526", fg="#9cdcfe", font=("Consolas", 10))
    expl_box.pack(fill=tk.X, pady=4)

    tk.Label(right, text="AI Suggested Fix / Candidate Code", bg="#1e1e1e", fg="white", font=("Arial", 11, "bold")).pack(anchor="w")
    fix_box = scrolledtext.ScrolledText(right, height=8, wrap=tk.NONE, bg="#252526", fg="#ce9178", font=("Consolas", 10))
    fix_box.pack(fill=tk.X, pady=4)

    last_fix: List[Optional[str]] = [None]

    def on_apply_fix():
        if last_fix[0]:
            editor.delete("1.0", tk.END)
            editor.insert("1.0", last_fix[0])
            status_lbl.config(text="Fix applied - click Run to execute")
        else:
            messagebox.showinfo("SEDS", "No candidate fix to apply.")

    fix_btns = tk.Frame(right, bg="#1e1e1e")
    fix_btns.pack(fill=tk.X, pady=4)
    tk.Button(fix_btns, text="Apply Fix", command=on_apply_fix, bg="#16a34a", fg="white", padx=10, pady=4).pack(side=tk.LEFT, padx=2)

    tk.Label(right, text="Terminal Output", bg="#1e1e1e", fg="white", font=("Arial", 11, "bold")).pack(anchor="w")
    term_box = scrolledtext.ScrolledText(right, wrap=tk.WORD, bg="#0c0c0c", fg="#00ff66", font=("Consolas", 10))
    term_box.pack(fill=tk.BOTH, expand=True, pady=4)

    def on_run():
        code = editor.get("1.0", "end-1c")
        term_box.delete("1.0", tk.END)
        expl_box.delete("1.0", tk.END)
        fix_box.delete("1.0", tk.END)
        last_fix[0] = None

        # Check static
        static_errs = ErrorDetector.detect_static(code)
        if any(e.severity == "error" for e in static_errs):
            err = static_errs[0]
            expl = ErrorExplainer.explain(err, code)
            fix = AutoFixer.generate_fix(err, code)
            status_lbl.config(text=f"Error: {err.error_type}")
            expl_box.insert(tk.END, f"1. WHAT: {expl.what}\\n2. WHERE: {expl.where}\\n3. WHY: {expl.why}\\n4. CAUSE: {expl.cause}\\n5. AFFECTED: {expl.affected}\\n6. HOW TO FIX: {expl.how_to_fix}\\n")
            if fix.fixed_code:
                last_fix[0] = fix.fixed_code
                fix_box.insert(tk.END, fix.fixed_code)
            term_box.insert(tk.END, f"Static Check Failed on Line {err.line}: {err.message}\\n")
            return

        res = CodeRunner.run_code(code)
        if res.stdout:
            term_box.insert(tk.END, res.stdout)
        if res.stderr:
            term_box.insert(tk.END, res.stderr)

        if res.exit_code == 0:
            status_lbl.config(text="Success (Exit 0)")
            expl_box.insert(tk.END, "Program executed successfully with 0 errors.\\n")
        else:
            all_errs = ErrorDetector.detect_all(code, runtime_stderr=res.stderr)
            if all_errs:
                err = all_errs[0]
                expl = ErrorExplainer.explain(err, code)
                fix = AutoFixer.generate_fix(err, code)
                status_lbl.config(text=f"Error: {err.error_type}")
                expl_box.insert(tk.END, f"1. WHAT: {expl.what}\\n2. WHERE: {expl.where}\\n3. WHY: {expl.why}\\n4. CAUSE: {expl.cause}\\n5. AFFECTED: {expl.affected}\\n6. HOW TO FIX: {expl.how_to_fix}\\n")
                if fix.fixed_code:
                    last_fix[0] = fix.fixed_code
                    fix_box.insert(tk.END, fix.fixed_code)

    def on_open():
        p = filedialog.askopenfilename(filetypes=[("Python files", "*.py"), ("All", "*.*")])
        if p:
            with open(p, "r", encoding="utf-8", errors="replace") as f:
                editor.delete("1.0", tk.END)
                editor.insert("1.0", f.read())

    def on_save():
        p = filedialog.asksaveasfilename(defaultextension=".py")
        if p:
            with open(p, "w", encoding="utf-8") as f:
                f.write(editor.get("1.0", "end-1c"))

    btn_bar = tk.Frame(left, bg="#1e1e1e")
    btn_bar.pack(fill=tk.X, pady=4)
    tk.Button(btn_bar, text="Run", command=on_run, bg="#0e639c", fg="white", padx=12, pady=4).pack(side=tk.LEFT, padx=2)
    tk.Button(btn_bar, text="Open", command=on_open, bg="#333", fg="white", padx=10, pady=4).pack(side=tk.LEFT, padx=2)
    tk.Button(btn_bar, text="Save", command=on_save, bg="#333", fg="white", padx=10, pady=4).pack(side=tk.LEFT, padx=2)
    tk.Button(btn_bar, text="Clear", command=lambda: editor.delete("1.0", tk.END), bg="#333", fg="white", padx=10, pady=4).pack(side=tk.LEFT, padx=2)

    root.mainloop()


# =============================================================================
# 11. MAIN LAUNCHER ENTRY POINT
# =============================================================================

def main():
    if "--tkinter" in sys.argv:
        print("[*] Starting SEDS in Native Tkinter Desktop Mode...")
        run_tkinter_gui()
        return

    print("=" * 65)
    print(" SMART ERROR DETECTION SYSTEM (SEDS) 2.0 - STANDALONE ALL-IN-ONE")
    print(" Tagline: Detect. Fix. Run. Automatically.")
    print("=" * 65)

    Database.init_db()
    port = int(os.getenv("PORT", os.getenv("SEDS_PORT", "5000")))
    host = os.getenv("SEDS_HOST", "0.0.0.0")
    url = f"http://127.0.0.1:{port}"

    print("[*] SQLite Database ready at seds.db")
    print(f"[*] SEDS Web IDE accessible at: {url}")
    print("[*] Press Ctrl+C in terminal to stop server.\\n")

    if "--no-browser" not in sys.argv:
        try:
            webbrowser.open(url)
        except Exception:
            pass

    app.run(host=host, port=port, debug=False)


if __name__ == "__main__":
    main()
