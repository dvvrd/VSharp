using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Reflection;
using VSharp.Core;
using NUnit.Framework;
using System.Text.RegularExpressions;
using Microsoft.FSharp.Core;


namespace VSharp.Test
{
    public class SVM
    {
        private ExplorerBase _explorer;

        public SVM(ExplorerBase explorer)
        {
            _explorer = explorer;
            API.Configure(explorer);
        }

        private codeLocationSummary PrepareAndInvoke(IDictionary<MethodInfo, codeLocationSummary> dict, MethodInfo m, Func<IMethodIdentifier, FSharpFunc<codeLocationSummary, codeLocationSummary>, codeLocationSummary> invoke)
        {
            IMethodIdentifier methodIdentifier = _explorer.MakeMethodIdentifier(m);
            if (methodIdentifier == null)
            {
                var format = new PrintfFormat<string, Unit, string, Unit>($"WARNING: metadata method for {m.Name} not found!");
                Logger.warning(format);
                return null;
            }
            dict?.Add(m, null);
            var id = FSharpFunc<codeLocationSummary,codeLocationSummary>.FromConverter(x => x);
            var summary = invoke(methodIdentifier, id);
            if (dict != null)
            {
                dict[m] = summary;
            }
            return summary;
        }

        private codeLocationSummary PrepareAndInvokeWithLogging(IDictionary<MethodInfo, codeLocationSummary> dict, MethodInfo m, Func<IMethodIdentifier, FSharpFunc<codeLocationSummary, codeLocationSummary>, codeLocationSummary> invoke)
        {
            IMethodIdentifier methodIdentifier = _explorer.MakeMethodIdentifier(m);
            if (methodIdentifier == null)
            {
                var format = new PrintfFormat<string, Unit, string, Unit>($"WARNING: metadata method for {m.Name} not found!");
                Logger.warning(format);
                return null;
            }
            dict?.Add(m, null);
            var id = FSharpFunc<codeLocationSummary,codeLocationSummary>.FromConverter(x => x);
            try
            {
                var summary = invoke(methodIdentifier, id);
                if (dict != null)
                {
                    dict[m] = summary;
                }
                return summary;
            }
            catch (Exception e)
            {
                var str = string.Format(@"For method {0} got exception {1}", m, e);
                PrintfFormat<Unit, Unit, string, Unit> printfFormat = new PrintfFormat<Unit, Unit, string, Unit>(str);
                Logger.error(printfFormat);
                return null;
            }
        }

        private void InterpretEntryPoint(IDictionary<MethodInfo, codeLocationSummary> dictionary, MethodInfo m)
        {
            Assert.IsTrue(m.IsStatic);
            PrepareAndInvoke(dictionary, m, _explorer.InterpretEntryPoint);
        }

        private void Explore(IDictionary<MethodInfo, codeLocationSummary> dictionary, MethodInfo m)
        {
            PrepareAndInvoke(dictionary, m, _explorer.Explore);
        }

        private void ExploreWithLogging(IDictionary<MethodInfo, codeLocationSummary> dictionary, MethodInfo m)
        {
            PrepareAndInvokeWithLogging(dictionary, m, _explorer.Explore);
        }

        private void ExploreType(List<string> ignoreList, MethodInfo ep, IDictionary<MethodInfo, codeLocationSummary> dictionary, Type t)
        {
            BindingFlags bindingFlags = BindingFlags.Instance | BindingFlags.Static | BindingFlags.Public | BindingFlags.DeclaredOnly;

            if (ignoreList?.Where(kw => !t.AssemblyQualifiedName.Contains(kw)).Count() == ignoreList?.Count && t.IsPublic)
            {
                foreach (var m in t.GetMethods(bindingFlags))
                {
                    if (m != ep && !m.IsAbstract)
                    {
                        Debug.Print(@"Called interpreter for method {0}", m.Name);
                        Explore(dictionary, m);
                    }
                }
            }
        }

        private static string ReplaceLambdaLines(string str)
        {
            return Regex.Replace(str, @"@\d+(\+|\-)\d*\[Microsoft.FSharp.Core.Unit\]", "");
        }

        private static string ResultToString(codeLocationSummary summary)
        {
            if (summary == null) return null;
            return $"{summary.result}\nHEAP:\n{ReplaceLambdaLines(API.Memory.Dump(summary.state))}";
        }

        public string ExploreOne(MethodInfo m)
        {
            var summary = PrepareAndInvoke(null, m, _explorer.Explore);
            return ResultToString(summary);
        }

        public void ConfigureSolver(ISolver solver)
        {
            API.ConfigureSolver(solver);
        }

        public IDictionary<MethodInfo, string> Run(Assembly assembly, List<string> ignoredList)
        {
            IDictionary<MethodInfo, codeLocationSummary> dictionary = new Dictionary<MethodInfo, codeLocationSummary>();
            var ep = assembly.EntryPoint;

            foreach (var t in assembly.GetTypes())
            {
                ExploreType(ignoredList, ep, dictionary, t);
            }

            if (ep != null)
            {
                InterpretEntryPoint(dictionary, ep);
            }

            foreach (var p in dictionary)
            {
                var str = string.Format(@"For method {0} got summary {1}", p.Key, ResultToString(p.Value));
                PrintfFormat<Unit, Unit, string, Unit> printfFormat = new PrintfFormat<Unit, Unit, string, Unit>(str);
                Logger.info(printfFormat);
            }

            return dictionary.ToDictionary(kvp => kvp.Key, kvp => ResultToString(kvp.Value));
        }

    }
}
