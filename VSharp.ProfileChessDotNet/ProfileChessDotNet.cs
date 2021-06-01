﻿using System;
using System.Reflection;
using VSharp.Analyzer;
using VSharp.Interpreter.IL;
using VSharp.Test;

namespace VSharp.ProfileChessDotNet
{
    class Program
    {
        static void Main(string[] args)
        {
            var bound = 15;
            var svm = new SVM(new MethodInterpreter(new ExceptionsExplorationSearcher(bound)));
            svm.ConfigureSolver();
            // var chessDotNetClass = typeof(Test.Tests.PDR);
            var chessDotNetType = typeof(Test.Tests.PDR);
            var chessDotNetMethod = chessDotNetType.GetMethod("BreakCallSitesCompositionRecursion");
            svm.ExploreOne(chessDotNetMethod);
        }
    }
}
