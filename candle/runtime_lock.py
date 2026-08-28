#!/usr/bin/env python3
"""Cooperative locking of an authenticated Candle build-directory inode."""

from __future__ import annotations

import fcntl
import os
from pathlib import Path
import stat
from typing import Any


class RuntimeLockError(ValueError):
    """The build lock could not be acquired without following a symlink."""


def _directory_flags() -> int:
    return (os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) |
            getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_CLOEXEC", 0))


class BuildLock:
    def __init__(self, fd: int, path: Path, exclusive: bool):
        self.fd = fd
        self.path = path
        self.exclusive = exclusive
        opened = os.fstat(fd)
        self.record: dict[str, Any] = {
            "path": str(path),
            "object": "directory_inode",
            "mode": "exclusive" if exclusive else "shared",
            "device": opened.st_dev,
            "inode": opened.st_ino,
        }

    def close(self) -> None:
        if self.fd >= 0:
            try:
                fcntl.flock(self.fd, fcntl.LOCK_UN)
            finally:
                os.close(self.fd)
                self.fd = -1

    def __del__(self) -> None:
        self.close()


def acquire_build_lock(candle_root: Path, *, exclusive: bool = False) -> BuildLock:
    """Open each path component without symlinks and lock the build inode."""

    candle_root = candle_root.resolve()
    flags = _directory_flags()
    root_fd = candle_fd = build_fd = -1
    try:
        root_fd = os.open(candle_root, flags)
        candle_fd = os.open("candle", flags, dir_fd=root_fd)
        build_fd = os.open("build", flags, dir_fd=candle_fd)
        opened = os.fstat(build_fd)
        if not stat.S_ISDIR(opened.st_mode):
            raise RuntimeLockError("Candle build lock object is not a directory")
        fcntl.flock(
            build_fd, fcntl.LOCK_EX if exclusive else fcntl.LOCK_SH,
        )
        current = os.stat("build", dir_fd=candle_fd, follow_symlinks=False)
        if (not stat.S_ISDIR(current.st_mode) or
                (current.st_dev, current.st_ino) !=
                (opened.st_dev, opened.st_ino)):
            raise RuntimeLockError(
                "Candle build directory changed while acquiring its lock"
            )
        result = BuildLock(
            build_fd, candle_root / "candle/build", exclusive,
        )
        build_fd = -1
        return result
    except (OSError, RuntimeLockError) as error:
        if isinstance(error, RuntimeLockError):
            raise
        raise RuntimeLockError(
            f"cannot acquire ordinary Candle build-directory lock: {error}"
        ) from error
    finally:
        for fd in (build_fd, candle_fd, root_fd):
            if fd >= 0:
                os.close(fd)
