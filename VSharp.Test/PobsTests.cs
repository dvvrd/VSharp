using System;
using System.Reflection;
using System.Diagnostics;
using System.Linq;

using NUnit.Framework;

using VSharp.Interpreter.IL;
using VSharp.Test.Tests;
using VSharp.Test.Tests.Pobs;

namespace VSharp.Test
{

    public class PobsSetup
    {

        static BindingFlags All =
            BindingFlags.IgnoreCase | BindingFlags.DeclaredOnly | BindingFlags.Instance |
            BindingFlags.Static | BindingFlags.NonPublic | BindingFlags.Public;
        public enum DesiredStatus
        {
            Witnessed
            , Unreachable
            , Unknown
        }
        public class CodeLocationProxy
        {
            public CodeLocationProxy(int offset, Type t, string methodName, DesiredStatus desiredStatus)
            {
                DesiredStatus = desiredStatus.ToString();
                Offset = offset;

                Method = t.GetMethod(methodName, All);
                Assert.IsNotNull(Method);
            }

            public int Offset { get; private set; }
            public string DesiredStatus { get; private set; }
            public MethodBase Method { get; private set; }
        }



        private static bool AnswerPobsForSearcher(MethodInfo entry, CodeLocationProxy[] proxies, INewSearcher searcher)
        {
            Core.codeLocation[] codeLocations = proxies.Select(p => new Core.codeLocation(p.Offset, p.Method)).ToArray();
            var svm = new SVM(new PobsInterpreter(searcher));
            svm.ConfigureSolver();
            // SVM.ConfigureSimplifier(new Z3Simplifier()); can be used to enable Z3-based simplification (not recommended)

            var stopWatch = new Stopwatch();
            stopWatch.Start();
            var dict = svm.AnswerPobs(entry, codeLocations);
            stopWatch.Stop();

            Console.WriteLine($"Searcher = {searcher.GetType()}, ElapsedTime = {stopWatch.Elapsed}");

            bool allWitnessed = true;
            foreach (var p in proxies)
            {
                var loc = new Core.codeLocation(p.Offset, p.Method);

                if (p.DesiredStatus != dict[loc])
                {
                    allWitnessed = false;
                    Console.WriteLine($"Searcher {searcher.GetType()} could not witness loc = {loc}");
                }
                // Assert.AreEqual(p.DesiredStatus, dict[loc], $"Checking location {loc}");
            }
            return allWitnessed;
        }

        [TestCaseSource(nameof(PobsCases))]
        public static void AnswerPobs(Type t, string mainName, CodeLocationProxy[] proxies)
        {
            int maxBound = 1000;
            var entryMethod = t.GetMethod(mainName, All);
            var searchers = new INewSearcher[]
            {
                new TargetedSearcher(maxBound)
                , new BFSSearcher(maxBound)
                , new DFSSearcher(maxBound)
            };

            bool allWitnessed = true;
            foreach (var s in searchers)
            {
                allWitnessed &= AnswerPobsForSearcher(entryMethod, proxies, s);
            }

            Assert.True(allWitnessed);
        }

        public static object[] PobsCases =
        {
            // first test case
            new object[]
            {
                typeof(SwitchWithSequentialCases1), nameof(SwitchWithSequentialCases1.EntryMethod),
                new []
                {
                    new CodeLocationProxy(56, typeof(SwitchWithSequentialCases1), nameof(SwitchWithSequentialCases1.EntryMethod), DesiredStatus.Witnessed),
                }
            }
            // second testCase
            , new object[]
            {
                typeof(CallsTest), nameof(CallsTest.EntryMethod2),
                new []
                {
                    new CodeLocationProxy(2, typeof(CallsTest), nameof(CallsTest.G), DesiredStatus.Witnessed)
                }
            }
            , new object[]
            {
                typeof(LotsOfIfs), nameof(LotsOfIfs.EntryMethod),
                new []
                {
                    new CodeLocationProxy(210, typeof(LotsOfIfs), nameof(LotsOfIfs.EntryMethod), DesiredStatus.Witnessed),
                }
            }
            , new object[]
            {
                typeof(UnsatCases), nameof(UnsatCases.EntryMethod),
                new []
                {
                    new CodeLocationProxy(23, typeof(UnsatCases), nameof(UnsatCases.EntryMethod), DesiredStatus.Unknown),
                }
            }
            , new object[]
            {
                typeof(Calls.Recursion), nameof(Calls.Recursion.F),
                new []
                {
                    new CodeLocationProxy(0xb, typeof(Calls.Recursion), nameof(Calls.Recursion.G), DesiredStatus.Witnessed),
                }
            }
            , new object[]
            {
                typeof(Calls.Recursion), nameof(Calls.Recursion.TrickyCycle),
                new []
                {
                    new CodeLocationProxy(0xb, typeof(Calls.Recursion), nameof(Calls.Recursion.G), DesiredStatus.Witnessed),
                }
            }
            , new object[]
            {
                typeof(SwitchWithSequentialCases1), nameof(SwitchWithSequentialCases1.SwitchWithExpensiveCalculations),
                new []
                {
                    new CodeLocationProxy(0x4a, typeof(SwitchWithSequentialCases1), nameof(SwitchWithSequentialCases1.SwitchWithExpensiveCalculations), DesiredStatus.Witnessed),
                }
            }

            , new object[]
            {
                typeof(SwitchWithSequentialCases1), nameof(SwitchWithSequentialCases1.TestForDFS),
                new []
                {
                    new CodeLocationProxy(0x56, typeof(SwitchWithSequentialCases1), nameof(SwitchWithSequentialCases1.TestForDFS), DesiredStatus.Witnessed),
                }
            }

            , new object[]
            {
                typeof(SwitchWithSequentialCases1), nameof(SwitchWithSequentialCases1.TrickyTestForTargetedSearcher),
                new []
                {
                    new CodeLocationProxy(0x1a, typeof(SwitchWithSequentialCases1), nameof(SwitchWithSequentialCases1.LittleExpensiveCalculations), DesiredStatus.Witnessed),
                }
            }

            , new object[]
            {
                typeof(SwitchWithSequentialCases1), nameof(SwitchWithSequentialCases1.BoundTest),
                new []
                {
                    new CodeLocationProxy(0x1e, typeof(SwitchWithSequentialCases1), nameof(SwitchWithSequentialCases1.BoundTest), DesiredStatus.Witnessed),
                }
            }

            , new object[]
            {
                typeof(ForKostya), nameof(ForKostya.SymbolicLinqTest2),
                new []
                {
                    // new CodeLocationProxy(0x009d, typeof(ForKostya), nameof(ForKostya.SymbolicLinqTest2), DesiredStatus.Witnessed),
                    new CodeLocationProxy(0x0079, typeof(ForKostya), nameof(ForKostya.SymbolicLinqTest2), DesiredStatus.Witnessed),
                }
            }

            , new object[]
            {
                typeof(ForKostya), nameof(ForKostya.SymbolicLinqTest),
                new []
                {
                    // new CodeLocationProxy(0x009d, typeof(ForKostya), nameof(ForKostya.SymbolicLinqTest2), DesiredStatus.Witnessed),
                    new CodeLocationProxy(0x007b, typeof(ForKostya), nameof(ForKostya.SymbolicLinqTest), DesiredStatus.Witnessed),
                    new CodeLocationProxy(0x0077, typeof(ForKostya), nameof(ForKostya.SymbolicLinqTest), DesiredStatus.Witnessed),
                }
            }

        };

    }



}
