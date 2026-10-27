#!/usr/bin/env python3
"""Install the local pre-commit launcher or check a fresh staged snapshot."""

import argparse
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile


MANAGED_LAUNCHER = b'''#!/bin/sh
set -eu
root=$(git rev-parse --show-toplevel)
exec sh "$root/.githooks/pre-commit" "$@"
'''


class HookError(Exception):
    """An installation or check failure suitable for a command-line diagnostic."""


def git(*arguments, cwd=None, check=True):
    try:
        result = subprocess.run(
            ["git", *arguments],
            cwd=cwd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            errors="replace",
        )
    except FileNotFoundError as error:
        raise HookError("Git is required; could not find 'git' on PATH.") from error
    if check and result.returncode:
        detail = result.stderr.strip() or result.stdout.strip()
        raise HookError("git {} failed:\n{}".format(" ".join(arguments), detail))
    return result


def install_launcher(path):
    """Create a launcher without following hook symlinks or replacing a hook."""
    parent = path.parent
    if parent.is_symlink():
        raise HookError("refusing symlinked hooks directory: {}".format(parent))
    parent.mkdir(parents=True, exist_ok=True)
    # Pin the directory and do not follow a hook symlink, including a dangling
    # one. Exclusive creation also prevents overwriting a concurrently added hook.
    directory_fd = os.open(parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        try:
            descriptor = os.open(
                path.name,
                os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                0o755,
                dir_fd=directory_fd,
            )
        except FileExistsError:
            created = False
            try:
                descriptor = os.open(
                    path.name,
                    os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW,
                    dir_fd=directory_fd,
                )
            except OSError as error:
                raise HookError(
                    "refusing existing hook at {}: {}".format(path, error)
                ) from error
        else:
            created = True

        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            os.close(descriptor)
            raise HookError("refusing non-regular hook at {}".format(path))
        try:
            with os.fdopen(descriptor, "wb" if created else "rb") as hook:
                if created:
                    hook.write(MANAGED_LAUNCHER)
                elif hook.read(len(MANAGED_LAUNCHER) + 1) != MANAGED_LAUNCHER:
                    raise HookError("refusing to overwrite existing hook: {}".format(path))
                os.fchmod(hook.fileno(), 0o755)
        except (OSError, HookError):
            if created:
                os.unlink(path.name, dir_fd=directory_fd)
            raise
    finally:
        os.close(directory_fd)
    return created


def install(root):
    configured = git("config", "--get-all", "core.hooksPath", cwd=root, check=False)
    if configured.returncode == 0:
        raise HookError(
            "core.hooksPath is configured ({!r}); refusing to install over a "
            "custom hook setup.".format(configured.stdout.rstrip("\n"))
        )
    if configured.returncode != 1:
        raise HookError("cannot query core.hooksPath:\n{}".format(configured.stderr.strip()))
    path = Path(git("rev-parse", "--git-path", "hooks/pre-commit", cwd=root).stdout.rstrip("\n"))
    if not path.is_absolute():
        path = root / path
    created = install_launcher(path)
    print("pre-commit: {} local launcher at {}".format(
        "installed" if created else "already installed", path
    ))
    return 0


def check(root):
    # checkout-index --all silently skips unmerged entries. Do not check an
    # incomplete snapshot if this command is called while a merge is unresolved.
    if git("ls-files", "--unmerged", "-z", cwd=root).stdout:
        raise HookError("cannot export staged snapshot: the index contains unmerged entries.")
    # Keep Git's index overrides for export (including a partial commit's
    # temporary index), but remove them before any checks start nested Git repos.
    child_env = os.environ.copy()
    for name in git("rev-parse", "--local-env-vars", cwd=root).stdout.splitlines():
        child_env.pop(name, None)

    with tempfile.TemporaryDirectory(prefix="refine-to-itree-staged-") as directory:
        git(
            "checkout-index",
            "--all",
            "--ignore-skip-worktree-bits",
            "--prefix", directory + os.sep,
            cwd=root,
        )
        try:
            result = subprocess.run(
                ["opam", "exec", "--", "make", "--no-print-directory", "-C", directory, "check"],
                # Resolve an active/local opam switch in the real repository,
                # before Make changes into the clean staged snapshot.
                cwd=root,
                env=child_env,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                errors="replace",
            )
        except FileNotFoundError as error:
            raise HookError("opam is required; could not find 'opam' on PATH.") from error

    if result.returncode:
        print("pre-commit: staged snapshot failed make check (exit {}).".format(
            result.returncode
        ), file=sys.stderr)
        if result.stdout:
            sys.stderr.write(result.stdout)
            if not result.stdout.endswith("\n"):
                sys.stderr.write("\n")
        return result.returncode if result.returncode > 0 else 1
    print("pre-commit: staged snapshot passed make check.")
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("install", "check"))
    arguments = parser.parse_args()
    try:
        root = Path(git("rev-parse", "--show-toplevel").stdout.rstrip("\n"))
        if arguments.command == "install":
            return install(root)
        return check(root)
    except (HookError, OSError) as error:
        print("pre-commit: {}".format(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
