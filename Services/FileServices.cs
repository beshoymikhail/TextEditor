using Microsoft.AspNetCore.Components.Forms;
using System.Reflection.Emit;
using System.Text.RegularExpressions;
using TextEditor.Model;

namespace TextEditor.Services
{
    public class FileServices : IFileServices
    {

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

            // Regular expression pattern to match lemma declarations
            string lemmaPattern = @"Lemma\s+\w+\s*(.*?)[\s\S]+?Qed\s*";

            // Find all matches of the lemmaPattern in the Coq code
            MatchCollection matches = Regex.Matches(extractedfile, lemmaPattern, RegexOptions.Singleline | RegexOptions.Multiline);
            int count = 1;
            // Print all matches
            foreach (Match match in matches)
            {
                var fun = match.Value.Split("Proof");
                functions.Add(new Function()
                {
                    Id = count,
                    Name = fun[0].Split("Lemma")[1],
                    Description = "Proof" + fun[1],
                    sourceFile=sourceFile,
                    FileName=file.Name,
                    FunctionType=FunctionType.Lemma
                });
                count++;
            }
            return functions;
        }
    }
}
