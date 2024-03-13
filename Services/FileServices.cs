using Microsoft.AspNetCore.Components.Forms;
using Microsoft.Extensions.FileSystemGlobbing;
using System.Diagnostics;
using System.IO;
using System.Reflection.Emit;
using System.Text.RegularExpressions;
using TextEditor.Model;

namespace TextEditor.Services
{
    public class FileServices : IFileServices
    {
        private static int count = 1;
        public async Task CopyFileToFolder(IBrowserFile file, string folderPath)
        {
            if (!Directory.Exists(folderPath))
            {
                Directory.CreateDirectory(folderPath);
            }
            using (var fileStream = new FileStream(Path.Combine(folderPath, file.Name), FileMode.Create))
            {
                await file.OpenReadStream().CopyToAsync(fileStream);
            }
        }

        public async Task<List<Function>> ExtractFile(IBrowserFile file, SourceFile sourceFile)
        {
            List<Function> functions = new List<Function>();
            string extractedfile = "";
            var stream = file.OpenReadStream();
            using (var reader = new StreamReader(stream))
            {
                extractedfile = await reader.ReadToEndAsync();
            }
            var lines = extractedfile.Trim().Split("\n\n");
            //Getting Lemmas
            var lemmas = GetLemmas(lines.Where(l => l.StartsWith(FunctionType.Lemma.ToString())).ToList(), sourceFile, file.Name);
            functions.AddRange(lemmas);
             //Getting Functions
            var _Functions_from_file = GetFunctiosEndWithDotAndEqual(lines.Where(l => l.StartsWith(FunctionType.Function.ToString())).ToList(),
                sourceFile, file.Name,FunctionType.Function);
            functions.AddRange(_Functions_from_file);    
            //Getting FixPoint
            var fixPoints = GetFunctiosEndWithDotAndEqual(lines.Where(l => l.StartsWith(FunctionType.Fixpoint.ToString())).ToList(),
                sourceFile, file.Name,FunctionType.Fixpoint);
            functions.AddRange(fixPoints);
            //Getting Definitions
            var definitions = GetFunctiosEndWithDotAndEqual(lines.Where(l => l.StartsWith(FunctionType.Definition.ToString())).ToList(),
                sourceFile, file.Name,FunctionType.Definition);
            functions.AddRange(definitions);
            return functions;
        }
        private List<Function> GetLemmas(List<string> functions, SourceFile sourceFile, string filename)
        {
            var Lemmas = new List<Function>();
            foreach (var function in functions)
            {
                string FunName = function.Split("Lemma")[1].Split("\n")[0];
                string description = "";
                string[] parts = FunName.Split(":");
                if (Regex.IsMatch(FunName, @"\b\w+\b\s*{[^{}]+}\s*\([^()]+\)\s*\([^()]+\)\s*\w*(?:\s*\w+)?"))
                {
                    // Split the function string at the last colon
                    FunName = parts.Length > 1 ? string.Join(":", parts, 0, parts.Length - 1) : function;
                }
                else if (Regex.IsMatch(FunName, @"\b\w+\b\s*{[^{}]+}\s*\w*(?:\s*\w+)?\s*\([^()]+\)\s*\w*(?:\s*\w+)?"))
                {
                    FunName = parts.Length > 1 ? string.Join(":", parts, 0, parts.Length - 1) : function;
                }
                else
                {
                    FunName = parts[0];
                }
                Lemmas.Add(
                    new Function()
                    {
                        Id = count,
                        Name = FunName,
                        Description = function.Split("Lemma")[1].Split(FunName)[1].Substring(2).Trim(),
                        sourceFile = sourceFile,
                        FileName = filename,
                        FunctionType = FunctionType.Lemma
                    });
                count++;
            }
            return Lemmas;
        }
        private List<Function> GetFunctiosEndWithDotAndEqual(List<string> functions, SourceFile sourceFile, string filename, FunctionType functionType)
        {
            var Functions = new List<Function>();
            foreach (var function in functions)
            {
                string[] Funparts = function.Split(functionType.ToString())[1].Split(":=");
                Functions.Add(
                    new Function()
                    {
                        Id = count,
                        Name = Funparts[0],
                        Description = Funparts[1].Substring(2).Trim(),
                        sourceFile = sourceFile,
                        FileName = filename,
                        FunctionType = functionType
                    });
                count++;
            }
            return Functions;
        }
    }
}
