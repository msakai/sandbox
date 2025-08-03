import os
import sys
import tempfile
from types import TracebackType
from typing import IO


class CaptureOutput:
  def __init__(self, output: str | None = None):
    self.output = output if output is not None else ""
    self._old_fd1: int | None = None
    self._old_fd2: int | None = None
    self._tmp_out: IO[str] | None = None

  def __enter__(self) -> "CaptureOutput":
    if self._old_fd1 is not None or self._old_fd2 is not None:
        raise RuntimeError("CaptureOutput is not reentrant")

    sys.stdout.flush()
    sys.stderr.flush()
    self._old_fd1 = os.dup(1)
    self._old_fd2 = os.dup(2)
    self._tmp_out = tempfile.TemporaryFile(mode='w+')
    os.dup2(self._tmp_out.fileno(), 1)
    os.dup2(self._tmp_out.fileno(), 2)

    return self

  def __exit__(self, exc_type: type[BaseException] | None, exc_value: BaseException | None, traceback: TracebackType | None) -> None:
      assert self._old_fd1 is not None
      assert self._old_fd2 is not None
      assert self._tmp_out is not None

      sys.stdout.flush()
      sys.stderr.flush()

      self._tmp_out.seek(0)
      self.output += self._tmp_out.read()

      os.dup2(self._old_fd1, 1)
      os.dup2(self._old_fd2, 2)
      os.close(self._old_fd1)
      os.close(self._old_fd2)

      self._old_fd1 = None
      self._old_fd2 = None
      self._tmp_out = None

      return None


cap = CaptureOutput()

with cap:
    print("Hello, ", file=sys.stderr)

with cap:
    print("World!")

print("==================")
print(cap.output)
print("==================")

