"""The batch checker must refuse a proof that states a different theorem (F9).

No Lean is needed: the statement binding is checked before any replay.
"""
import json
import subprocess
import sys
from pathlib import Path

CHECKER = Path(__file__).resolve().parents[1] / "scripts" / "lean_replay_checker.py"


def test_a_mismatched_statement_is_refused(tmp_path):
    proof = tmp_path / "proof.lean"
    proof.write_text("import Mathlib\n\ntheorem other : 1 + 1 = 2 := by norm_num\n",
                     encoding="utf-8")
    contract = {"task_id": "t1", "node": {"quantifier": "universal",
                                          "lean_statement": "theorem wanted : 2 + 2 = 4"},
                "input_artifacts": [{"id": "a" * 64, "path": str(proof)}],
                "result_contract": {"task_id": "t1", "statement_digest": "d" * 64}}
    path = tmp_path / "input.json"
    path.write_text(json.dumps(contract), encoding="utf-8")
    proc = subprocess.run([sys.executable, str(CHECKER), str(path)], cwd=tmp_path,
                          capture_output=True, text=True, encoding="utf-8", errors="replace")
    assert proc.returncode != 0
    assert "does not state the node's Lean declaration" in proc.stderr
    assert not (tmp_path / "result.json").exists()


def test_a_declared_theorem_must_be_checkable(tmp_path, monkeypatch):
    """If Lean cannot #check the declared name, the checker refuses (F9)."""
    import os
    proof = tmp_path / "proof.lean"
    proof.write_text("import Mathlib\n\ntheorem wanted : 2 + 2 = 4 := by norm_num\n",
                     encoding="utf-8")
    contract = {"task_id": "t1", "node": {"quantifier": "universal",
                                          "lean_statement": "theorem wanted : 2 + 2 = 4"},
                "input_artifacts": [{"id": "a" * 64, "path": str(proof)}],
                "result_contract": {"task_id": "t1", "statement_digest": "d" * 64}}
    path = tmp_path / "input.json"
    path.write_text(json.dumps(contract), encoding="utf-8")
    stub = tmp_path / "lean.bat"
    stub.write_text("@echo off\necho unknown identifier\nexit /b 1\n", encoding="utf-8")
    monkeypatch.setenv("AI4MATH_LEAN_PROJECT", str(tmp_path / "nope"))
    monkeypatch.setenv("PATH", str(tmp_path) + ";" + os.environ["PATH"])
    proc = subprocess.run([sys.executable, str(CHECKER), str(path)], cwd=tmp_path,
                          capture_output=True, text=True, encoding="utf-8", errors="replace")
    assert proc.returncode != 0
    assert "could not #check" in proc.stderr
    assert not (tmp_path / "result.json").exists()


def test_a_mismatched_lean_type_is_refused(tmp_path, monkeypatch):
    """When the node declares lean_type, Lean's printed type must match it (F9)."""
    import os
    proof = tmp_path / "proof.lean"
    proof.write_text("import Mathlib\n\ntheorem wanted : 2 + 2 = 4 := by norm_num\n",
                     encoding="utf-8")
    contract = {"task_id": "t1",
                "node": {"quantifier": "universal",
                         "lean_statement": "theorem wanted : 2 + 2 = 4",
                         "lean_type": "3 + 3 = 6"},
                "input_artifacts": [{"id": "a" * 64, "path": str(proof)}],
                "result_contract": {"task_id": "t1", "statement_digest": "d" * 64}}
    path = tmp_path / "input.json"
    path.write_text(json.dumps(contract), encoding="utf-8")
    stub = tmp_path / "lean.bat"
    stub.write_text("@echo off\necho wanted : 2 + 2 = 4\nexit /b 0\n", encoding="utf-8")
    monkeypatch.setenv("AI4MATH_LEAN_PROJECT", str(tmp_path / "nope"))
    monkeypatch.setenv("PATH", str(tmp_path) + ";" + os.environ["PATH"])
    proc = subprocess.run([sys.executable, str(CHECKER), str(path)], cwd=tmp_path,
                          capture_output=True, text=True, encoding="utf-8", errors="replace")
    assert proc.returncode != 0
    assert "does not match the node's declared lean_type" in proc.stderr


def test_a_sorry_axiom_is_refused(tmp_path, monkeypatch):
    """A kernel-checked proof that still uses sorryAx is not a proof (F9)."""
    import os
    proof = tmp_path / "proof.lean"
    proof.write_text("import Mathlib\n\ntheorem wanted : 2 + 2 = 4 := by sorry\n",
                     encoding="utf-8")
    contract = {"task_id": "t1", "node": {"quantifier": "universal",
                                          "lean_statement": "theorem wanted : 2 + 2 = 4"},
                "input_artifacts": [{"id": "a" * 64, "path": str(proof)}],
                "result_contract": {"task_id": "t1", "statement_digest": "d" * 64}}
    path = tmp_path / "input.json"
    path.write_text(json.dumps(contract), encoding="utf-8")
    stub = tmp_path / "lean.bat"
    stub.write_text("@echo off\necho axioms: [propext, sorryAx]\nexit /b 0\n", encoding="utf-8")
    monkeypatch.setenv("AI4MATH_LEAN_PROJECT", str(tmp_path / "nope"))
    monkeypatch.setenv("PATH", str(tmp_path) + ";" + os.environ["PATH"])
    proc = subprocess.run([sys.executable, str(CHECKER), str(path)], cwd=tmp_path,
                          capture_output=True, text=True, encoding="utf-8", errors="replace")
    assert proc.returncode != 0
    assert "sorryAx" in proc.stderr
    assert not (tmp_path / "result.json").exists()


def test_a_matching_statement_passes_the_binding_check(tmp_path, monkeypatch):
    import os
    proof = tmp_path / "proof.lean"
    proof.write_text("import Mathlib\n\ntheorem wanted : 2 + 2 = 4 := by norm_num\n",
                     encoding="utf-8")
    contract = {"task_id": "t1", "node": {"quantifier": "universal",
                                          "lean_statement": "theorem wanted : 2 + 2 = 4"},
                "input_artifacts": [{"id": "a" * 64, "path": str(proof)}],
                "result_contract": {"task_id": "t1", "statement_digest": "d" * 64}}
    path = tmp_path / "input.json"
    path.write_text(json.dumps(contract), encoding="utf-8")
    # Point the checker at a non-existent project so it uses the lean on PATH, and make
    # lean a no-op stub: this test only covers the binding, not the replay.
    stub = tmp_path / "lean.bat"
    stub.write_text("@echo off\necho Lean (version 4.test)\nexit /b 0\n", encoding="utf-8")
    monkeypatch.setenv("AI4MATH_LEAN_PROJECT", str(tmp_path / "nope"))
    monkeypatch.setenv("PATH", str(tmp_path) + ";" + __import__("os").environ["PATH"])
    proc = subprocess.run([sys.executable, str(CHECKER), str(path)], cwd=tmp_path,
                          capture_output=True, text=True, encoding="utf-8", errors="replace")
    assert proc.returncode == 0, proc.stderr
    result = json.loads((tmp_path / "result.json").read_text(encoding="utf-8"))
    assert result["passed"] is True
