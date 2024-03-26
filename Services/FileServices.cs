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
            foreach (var file in files)
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
            //Getting Program FixPoint
            var ProgramFixPoints = lines.Where(l => l.StartsWith(StructureType.ProgramFixpoint.GetDisplayName())).ToList();
            if (ProgramFixPoints.Count() > 0)
            {
                functions.AddRange(GetStructuresEndWithDotAndEqual(ProgramFixPoints, sourceFile, StructureType.ProgramFixpoint));
            }
            //Getting Definitions
            var definitions = lines.Where(l => l.StartsWith(StructureType.Definition.GetDisplayName())).ToList();
            if (definitions.Count() > 0)
            {
                functions.AddRange(GetStructuresEndWithDotAndEqual(definitions, sourceFile, StructureType.Definition));
            }
            //Getting Program Definitions
            var ProgramDefinitions = lines.Where(l => l.StartsWith(StructureType.ProgramDefinition.GetDisplayName())).ToList();
            if (ProgramDefinitions.Count() > 0)
            {
                functions.AddRange(GetStructuresEndWithDotAndEqual(ProgramDefinitions, sourceFile, StructureType.ProgramDefinition));
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
            //Getting Classes
            var Classes = lines.Where(l => l.StartsWith(StructureType.Class.GetDisplayName())).ToList();
            if (Classes.Count() > 0)
            {
                functions.AddRange(GetStructuresEndWithDotAndEqual(Classes, sourceFile, StructureType.Class));
            }
            //Getting Inductives 
            var Inductives = lines.Where(l => l.StartsWith(StructureType.Inductive.GetDisplayName())).ToList();
            if (Inductives.Count() > 0)
            {
                functions.AddRange(GetStructuresEndWithDotAndEqual(Inductives, sourceFile, StructureType.Inductive));
            }
            //Getting Theoremses
            var Theorems = lines.Where(l => l.StartsWith(StructureType.Theorem.GetDisplayName())).ToList();
            if (Theorems.Count() > 0)
            {
                functions.AddRange(GetTheorem(Theorems, sourceFile, StructureType.Theorem));
            }
            //Getting Facts 
            var Facts = lines.Where(l => l.StartsWith(StructureType.Fact.GetDisplayName())).ToList();
            if (Facts.Count() > 0)
            {
                functions.AddRange(GetFacts(Facts, sourceFile, StructureType.Fact));
            }
            //Getting Remarks 
            var Remarks = lines.Where(l => l.StartsWith(StructureType.Remark.GetDisplayName())).ToList();
            if (Remarks.Count() > 0)
            {
                functions.AddRange(GetRemarks(Remarks, sourceFile, StructureType.Remark));
            }
            //Getting Corollaries
            var Corollaries = lines.Where(l => l.StartsWith(StructureType.Corollary.GetDisplayName())).ToList();
            if (Corollaries.Count() > 0)
            {
                functions.AddRange(GetCorollaries(Corollaries, sourceFile, StructureType.Corollary));
            }
            //Getting Propositions 
            var Propositions = lines.Where(l => l.StartsWith(StructureType.Proposition.GetDisplayName())).ToList();
            if (Propositions.Count() > 0)
            {
                functions.AddRange(GetPropositions(Propositions, sourceFile, StructureType.Proposition));
            }
            //Getting Properties Waiting
            var Properties = lines.Where(l => l.StartsWith(StructureType.Property.GetDisplayName())).ToList();
            if (Properties.Count() > 0)
            {
                functions.AddRange(GetProperties(Properties, sourceFile, StructureType.Property));
            }
            return functions;
        }
        private List<Structure> GetLemmas(List<string> functions, SourceFile sourceFile)
        {
            var Lemmas = new List<Structure>();
            foreach (var function in functions)
            {
                string FunName = function.Split("Lemma")[1].Split("\n")[0];
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
            foreach (var structure in structures)
            {
                string[] Funparts = structure.Split(StructureType.ToString())[1].Split(":=");
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
        private List<Structure> GetFacts(List<string> structures, SourceFile sourceFile, StructureType StructureType)
        {
            var Structures = new List<Structure>();
            foreach (var structure in structures)
            {
                string[] Funparts = structure.Split(StructureType.ToString())[1].Split(": nat");
                Structures.Add(
                    new Structure()
                    {
                        Id = count,
                        Name = Funparts[0],
                        Description = "nat" + Funparts[1].Substring(2).Trim(),
                        sourceFile = sourceFile,
                        StructureType = StructureType
                    });
                count++;
            }
            return Structures;
        } 
        private List<Structure> GetTheorem(List<string> structures, SourceFile sourceFile, StructureType StructureType)
        {
            var Structures = new List<Structure>();
            foreach (var structure in structures)
            {
                string[] Funparts = structure.Split(StructureType.ToString())[1].Split(": nat");
                Structures.Add(
                    new Structure()
                    {
                        Id = count,
                        Name = Funparts[0],
                        Description = "nat" + Funparts[1].Substring(2).Trim(),
                        sourceFile = sourceFile,
                        StructureType = StructureType
                    });
                count++;
            }
            return Structures;
        } 
        private List<Structure> GetRemarks(List<string> structures, SourceFile sourceFile, StructureType StructureType)
        {
            var Structures = new List<Structure>();
            foreach (var structure in structures)
            {
                string[] Funparts = structure.Split(StructureType.ToString())[1].Split(": Type");
                Structures.Add(
                    new Structure()
                    {
                        Id = count,
                        Name = Funparts[0],
                        Description =  "Type"+ Funparts[1].Substring(2).Trim(),
                        sourceFile = sourceFile,
                        StructureType = StructureType
                    });
                count++;
            }
            return Structures;
        }  
        private List<Structure> GetCorollaries(List<string> structures, SourceFile sourceFile, StructureType StructureType)
        {
            var Structures = new List<Structure>();
            foreach (var structure in structures)
            {
                string[] Funparts = structure.Split(StructureType.ToString())[1].Split(": Type");
                Structures.Add(
                    new Structure()
                    {
                        Id = count,
                        Name = Funparts[0],
                        Description =  "Type"+ Funparts[1].Substring(2).Trim(),
                        sourceFile = sourceFile,
                        StructureType = StructureType
                    });
                count++;
            }
            return Structures;
        }
         private List<Structure> GetPropositions(List<string> structures, SourceFile sourceFile, StructureType StructureType)
        {
            var Structures = new List<Structure>();
            foreach (var structure in structures)
            {
                string[] Funparts = structure.Split(StructureType.ToString())[1].Split(": Type");
                Structures.Add(
                    new Structure()
                    {
                        Id = count,
                        Name = Funparts[0],
                        Description =  "Type"+ Funparts[1].Substring(2).Trim(),
                        sourceFile = sourceFile,
                        StructureType = StructureType
                    });
                count++;
            }
            return Structures;
        } 
        private List<Structure> GetProperties(List<string> structures, SourceFile sourceFile, StructureType StructureType)
        {
            var Structures = new List<Structure>();
            foreach (var structure in structures)
            {
                string[] Funparts = structure.Split(StructureType.ToString())[1].Split(": Type");
                Structures.Add(
                    new Structure()
                    {
                        Id = count,
                        Name = Funparts[0],
                        Description =  "Type"+ Funparts[1].Substring(2).Trim(),
                        sourceFile = sourceFile,
                        StructureType = StructureType
                    });
                count++;
            }
            return Structures;
        }

        public string ReadFileAsString(string FilePath)
        {
            if (File.Exists(FilePath))
            {
                return File.ReadAllText(FilePath).ToString();
            }
            return "File Not Found";
        }
    }
}
