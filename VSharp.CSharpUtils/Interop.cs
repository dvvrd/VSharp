using System;

namespace VSharp.CSharpUtils
{
    public unsafe class Interop
    {
        [Implements("System.Int32 Interop+Kernel32.LCMapStringEx(System.String, System.UInt32, System.Char*, System.Int32, System.Void*, System.Int32, System.Void*, System.Void*, System.IntPtr)")]
        public static int LCMapStringEx(string a, uint b, char* c, int d, void* e, int f, void* g, void* h, IntPtr i)
        {
            return 0;
        }
    }
}
