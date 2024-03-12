using Microsoft.AspNetCore.Components.Forms;
using Microsoft.Extensions.FileSystemGlobbing;
using System.Diagnostics;
using System.Reflection.Emit;
using System.Text.RegularExpressions;
using TextEditor.Model;

namespace TextEditor.Services
{
    public class FileServices : IFileServices
    {
        private static int count=1;
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
            var lemmas = GetLemmas(lines.Where(l => l.StartsWith(FunctionType.Lemma.ToString())).ToList(),sourceFile,file.Name);
            functions.AddRange(lemmas);
            foreach (var m in lines)
            {
                Console.WriteLine(m);
            }
            // Regular expression pattern to match lemma declarations
            string lemmaPattern = @"Lemma\s+\w+\s*(.*?)[\s\S]+?Qed\s*";

            // Find all matches of the lemmaPattern in the Coq code
            MatchCollection matches = Regex.Matches(extractedfile, lemmaPattern, RegexOptions.Singleline | RegexOptions.Multiline);
           
            // Print all matches
           
            return functions;
        }
        private List<Function> GetLemmas(List<string> functions,SourceFile sourceFile,string filename)
        {
            var Lemmas = new List<Function>();
            foreach (var function in functions)
            {
                var fun = function.Split("Proof");

                Lemmas.Add(new Function()
                {
                    Id = count,
                    Name = fun[0].Split("Lemma")[1],
                    Description = "Proof" + fun[1],
                    sourceFile = sourceFile,
                    FileName = filename,
                    FunctionType = FunctionType.Lemma
                });
                count++;
            }
            return Lemmas;
        }
             

    }
}
