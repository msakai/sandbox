import ctypes
from ctypes import wintypes

dll = ctypes.WinDLL("./hello.dll")

hello = dll.hello
hello.argtypes = [wintypes.LPCWSTR]
hello.restype = None

hello("ABCあいうえお❤️")
