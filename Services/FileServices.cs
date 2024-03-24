using Microsoft.AspNetCore.Components.Forms;
using System.Text.RegularExpressions;
using TextEditor.Model;

namespace TextEditor.Services
{
    public class FileServices : IFileServices
    {
        private static int count { get; set; } = 1;

        public async Task<string> CreatingSavedFile(string folderPath, string folderName)
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
            return filePath;
        }
        public async Task<List<string>> CopyFileToFolder(List<IBrowserFile> files, string folderPath)
        {
            List<string> result = new List<string>();
            if (!Directory.Exists(folderPath))
            {
                Directory.CreateDirectory(folderPath);
            }
            foreach (IBrowserFile file in files)
            {
                using (var fileStream = new FileStream(Path.Combine(folderPath, file.Name), FileMode.Create))
                {
                    await file.OpenReadStream().CopyToAsync(fileStream);
                    result.Add(file.Name);
                }
            }
            return result;
        }

        public async Task<List<Structure>> ExtractFile(List<string> files, SourceFile sourceFile, string folderPath)
        {
            List<Structure> functions = new List<Structure>();
            string extractedfile = "";
            foreach (var file in files)
            {
                var readFile = Path.Combine(folderPath, file);
                extractedfile += File.ReadAllText(readFile);

            }
            var lines = extractedfile.Trim().Split("\n\n");
            //Getting Lemmas
            var lemmas = GetLemmas(lines.Where(l => l.StartsWith(StructureType.Lemma.GetDisplayName())).ToList(), sourceFile);
            functions.AddRange(lemmas);
            //Getting Functions
            var linefunctions = lines.Where(l => l.StartsWith(StructureType.Function.GetDisplayName())).ToList();
            if (linefunctions.Count() > 0)
            {
                functions.AddRange(GetStructuresEndWithDotAndEqual(linefunctions, sourceFile, StructureType.Function));
            }
            //Getting FixPoint
            var fixPoints = lines.Where(l => l.StartsWith(StructureType.Fixpoint.GetDisplayName())).ToList();
            if (fixPoints.Count() > 0)
            {
                functions.AddRange(GetStructuresEndWithDotAndEqual(fixPoints, sourceFile, StructureType.Fixpoint));
            }
            //Getting Definitions
            var definitions = lines.Where(l => l.StartsWith(StructureType.Definition.GetDisplayName())).ToList();
            if (definitions.Count() > 0)
            {
                functions.AddRange(GetStructuresEndWithDotAndEqual(definitions, sourceFile, StructureType.Definition));
            }
            //Getting Records
            var Records = lines.Where(l => l.StartsWith(StructureType.Record.GetDisplayName())).ToList();
            if (Records.Count() > 0)
            {
                functions.AddRange(GetStructuresEndWithDotAndEqual(Records, sourceFile, StructureType.Record));
            }
            //Getting Canonicals 
            var Canonicals = lines.Where(l => l.StartsWith(StructureType.Canonical.GetDisplayName())).ToList();
            if (Canonicals.Count() > 0)
            {
                functions.AddRange(GetStructuresEndWithDotAndEqual(Canonicals, sourceFile, StructureType.Canonical));
            }
            return functions;
        }
        private List<Structure> GetLemmas(List<string> functions, SourceFile sourceFile)
        {
            var Lemmas = new List<Structure>();
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
                    new Structure()
                    {
                        Id = count,
                        Name = FunName,
                        Description = function.Split("Lemma")[1].Split(FunName)[1].Substring(2).Trim(),
                        sourceFile = sourceFile,
                        StructureType = StructureType.Lemma
                    });
                count++;
            }
            return Lemmas;
        }
        private List<Structure> GetStructuresEndWithDotAndEqual(List<string> structures, SourceFile sourceFile, StructureType StructureType)
        {
            var Structures = new List<Structure>();
            foreach (var function in structures)
            {
                string[] Funparts = function.Split(StructureType.ToString())[1].Split(":=");
                Structures.Add(
                    new Structure()
                    {
                        Id = count,
                        Name = Funparts[0],
                        Description = Funparts[1].Substring(2).Trim(),
                        sourceFile = sourceFile,
                        StructureType = StructureType
                    });
                count++;
            }
            return Structures;
        }

        public async Task<string> ReadFileAsString(string FilePath)
        {
            if (File.Exists(FilePath))
            {
                return File.ReadAllText(FilePath).ToString();
            }
            return "File Not Found";
        }
    }
}
