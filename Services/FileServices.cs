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
        private static int count { get; set; } = 1;

        public async Task CreatingSavedFile(string folderPath, string folderName)
        {
            string fileName = folderName + ".fv";
            string filePath = Path.Combine(folderPath, fileName);
            // Create the directory if it doesn't exist
            if (!Directory.Exists(folderPath))
            {
                Directory.CreateDirectory(folderPath);
            }
            if (!File.Exists(filePath))
            {
                using (FileStream fs = File.Create(filePath))
                {
                    // You can write to the file if needed
                }

            }
        }
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
            var lemmas = GetLemmas(lines.Where(l => l.StartsWith(FunctionType.Lemma.GetDisplayName())).ToList(), sourceFile, file.Name);
            functions.AddRange(lemmas);
            //Getting Functions
            var linefunctions = lines.Where(l => l.StartsWith(FunctionType.Function.GetDisplayName())).ToList();
            if (linefunctions.Count() > 0)
            {
                functions.AddRange(GetFunctiosEndWithDotAndEqual(linefunctions, sourceFile, file.Name, FunctionType.Function));
            }
            //Getting FixPoint
            var fixPoints = lines.Where(l => l.StartsWith(FunctionType.Fixpoint.GetDisplayName())).ToList();
            if (fixPoints.Count() > 0)
            {
                functions.AddRange(GetFunctiosEndWithDotAndEqual(fixPoints, sourceFile, file.Name, FunctionType.Fixpoint));
            }
            //Getting Definitions
            var definitions = lines.Where(l => l.StartsWith(FunctionType.Definition.GetDisplayName())).ToList();
            if (definitions.Count() > 0)
            {
                functions.AddRange(GetFunctiosEndWithDotAndEqual(definitions, sourceFile, file.Name, FunctionType.Definition));
            }
            //Getting Records
            var Records = lines.Where(l => l.StartsWith(FunctionType.Record.GetDisplayName())).ToList();
            if (Records.Count() > 0)
            {
                functions.AddRange(GetFunctiosEndWithDotAndEqual(Records, sourceFile, file.Name, FunctionType.Record));
            }
            //Getting Canonicals 
            var Canonicals = lines.Where(l => l.StartsWith(FunctionType.Canonical.GetDisplayName())).ToList();
            if (Canonicals.Count() > 0)
            {
                functions.AddRange(GetFunctiosEndWithDotAndEqual(Canonicals, sourceFile, file.Name, FunctionType.Canonical));
            }
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
