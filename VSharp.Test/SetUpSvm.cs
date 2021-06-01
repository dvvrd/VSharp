using System;
using System.Diagnostics;
using System.Globalization;
using System.Threading;
using NUnit.Framework;
using VSharp.Analyzer;
using VSharp.Interpreter.IL;

namespace VSharp.Test
{
    [SetUpFixture]
    public class SetUpSvm
    {
        [OneTimeSetUp]
        public void PrepareSvm()
        {
            Trace.Listeners.Add(new Utils.DumpStackTraceListener());

            var ci = new CultureInfo("en-GB")
            {
                NumberFormat = {
                    PositiveInfinitySymbol = "Infinity",
                    NegativeInfinitySymbol = "-Infinity"
                }
            };
            Thread.CurrentThread.CurrentCulture = ci;

            var bound = 20;
            // var svm = new SVM(new VSharp.Analyzer.StepInterpreter());
            // var svm = new SVM(new MethodInterpreter(new MethodSearcher()));
            Logger.ConfigureWriter(TestContext.Progress);
            // var svm = new SVM(new PobsInterpreter(new BFSSearcher(bound)));
            // var svm = new SVM(new PobsInterpreter(new DFSSearcher(bound)));
            var svm = new SVM(new PobsInterpreter(new TargetedSearcher(bound)));
            // var svm = new SVM(new MethodInterpreter(new BFSSearcher(bound)));
            svm.ConfigureSolver();
            // SVM.ConfigureSimplifier(new Z3Simplifier()); can be used to enable Z3-based simplification (not recommended)
            var maxBound = 20;
            var searchers = new INewSearcher[] {
                new DFSSearcher(maxBound), new TargetedSearcher(maxBound), new BFSSearcher(maxBound)
            };
            var pobsStatistics = new PobsStatistics(searchers);
            TestSvmAttribute.SetUpSVM(svm, maxBound, searchers, pobsStatistics);
        }

        [OneTimeTearDown]
        public void PrintStats()
        {
            TestSvmAttribute.PrintStats();
        }

    }
}