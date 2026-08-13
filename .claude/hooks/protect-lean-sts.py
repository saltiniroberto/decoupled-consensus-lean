#!/usr/bin/env python3
"""Refuse to push to the `lean-sts` remote, or to write inside its submodule.

`deps/lean-sts` is a git submodule of https://github.com/saltiniroberto/lean-sts, which is
a separate project with its own history.  A push from inside a submodule goes to that
remote, not to this repository's, so a stray `git push` here publishes to the framework
repository.  This hook is what stops that; it is not a reminder, it denies the tool call.

It also refuses writes under `deps/lean-sts/`.  That is a checkout of another project -- edit it
in its own working copy of that repository, where the change can be committed and pushed
deliberately, and then move this project's submodule pointer.

Wired up by `.claude/settings.json` as a `PreToolUse` hook on `Bash` and on the file-editing
tools.  Exit 2 denies the call and shows stderr to the model; exit 0 allows it.
"""

from __future__ import annotations

import json
import os
import re
import sys
from pathlib import Path

# The submodule, and the strings that give away an attempt to reach it.
SUBMODULE = "deps/lean-sts"
GIVEAWAYS = ("lean-sts", "saltiniroberto")

WRITE_TOOLS = {"Edit", "Write", "NotebookEdit", "MultiEdit"}


def project_dir() -> Path:
    env = os.environ.get("CLAUDE_PROJECT_DIR")
    if env:
        return Path(env).resolve()
    return Path(__file__).resolve().parents[2]


def deny(message: str) -> None:
    print(message, file=sys.stderr)
    sys.exit(2)


def under(path: Path, base: Path) -> bool:
    try:
        path.resolve().relative_to(base.resolve())
        return True
    except (ValueError, OSError):
        return False


def check_bash(command: str, cwd: str, root: Path) -> None:
    # `git subtree push`, `git -C <dir> push`, `git push`: all of them contain both words.
    if not re.search(r"(?<![\w-])push(?![\w-])", command):
        return
    if not re.search(r"(?<![\w-])git(?![\w-])", command):
        return

    reasons = []
    if any(g in command for g in GIVEAWAYS):
        reasons.append("the command names lean-sts")
    if re.search(r"submodule\s+foreach", command):
        reasons.append("`git submodule foreach` would run inside deps/lean-sts")
    if cwd and under(Path(cwd), root / SUBMODULE):
        reasons.append(f"the shell's working directory is inside {SUBMODULE}")
    if not reasons:
        return

    deny(
        "DENIED: this looks like a push to https://github.com/saltiniroberto/lean-sts "
        f"({'; '.join(reasons)}).\n"
        f"{SUBMODULE} is a submodule of that separate repository, so a push from inside it "
        "publishes to the framework project.\n"
        "Do not retry with a different spelling. If the push is intended, Roberto runs it "
        f"himself, from his own terminal, in {SUBMODULE} or in a working copy of that\n"
        "repository.\n"
        "To change which revision this project builds against, check out the commit in "
        f"{SUBMODULE} and commit the submodule pointer here -- that needs no push."
    )


def check_write(file_path: str, root: Path) -> None:
    if not file_path:
        return
    target = Path(file_path)
    if under(target, root / SUBMODULE):
        deny(
            f"DENIED: {file_path} is inside {SUBMODULE}, a checkout of the separate "
            "lean-sts repository.\n"
            "Edit the framework in its own working copy of that repository, where the "
            "change can be committed and pushed deliberately. Then move this project's "
            "submodule pointer to the new revision."
        )


def main() -> int:
    try:
        data = json.load(sys.stdin)
    except (json.JSONDecodeError, ValueError):
        return 0  # Malformed input is not grounds to block a call.

    tool = data.get("tool_name", "")
    tool_input = data.get("tool_input") or {}
    root = project_dir()

    if tool == "Bash":
        check_bash(str(tool_input.get("command", "")), str(data.get("cwd", "")), root)
    elif tool in WRITE_TOOLS:
        check_write(str(tool_input.get("file_path", "")), root)

    return 0


if __name__ == "__main__":
    sys.exit(main())
