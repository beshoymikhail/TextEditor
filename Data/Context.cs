using Microsoft.AspNetCore.Components.Forms;
using System;
using TextEditor.Model;

namespace TextEditor.Data
{
    public class Context
    {
        public string? Introduction { get; set; }
        public List<Structure> structures { get; set; } = new List<Structure>();
        public IDictionary<DocumentationType, Documentation> Documentations { get; set; } = new Dictionary<DocumentationType, Documentation>
        {
            { DocumentationType.DataTypes,new Documentation(){DocumentationText="",DocumentationStructures=new List<Structure>()} },
            { DocumentationType.AdmittedLemmas,new Documentation(){DocumentationText="",DocumentationStructures=new List<Structure>()} },
            { DocumentationType.MainFunctions,new Documentation(){DocumentationText="",DocumentationStructures=new List<Structure>()} },
            { DocumentationType.SupportFunctions,new Documentation(){DocumentationText="",DocumentationStructures=new List<Structure>()} },
            { DocumentationType.AuxiliaryFunctions,new Documentation(){DocumentationText="",DocumentationStructures=new List<Structure>()} },
            { DocumentationType.OtherRelevantFunctions,new Documentation(){DocumentationText="",DocumentationStructures=new List<Structure>()} },
        };
        public IDictionary<string, List<IBrowserFile>> uploaded_files { get; set; } = new Dictionary<string, List<IBrowserFile>>
           { { "auxiliaryfile",new List<IBrowserFile>() }, { "implementationfile", new List < IBrowserFile>() }, { "specificationfile", new List < IBrowserFile>() } };
         public IDictionary<string, List<string>> saved_uploaded_files { get; set; } = new Dictionary<string, List<string>>
           { { "auxiliaryfile",new List<string>() }, { "implementationfile", new List < string>() }, { "specificationfile", new List < string>() } };
        public string FolderPath { get; set; } = string.Empty;
        public string FolderName { get; set; } = string.Empty;
        public string FullFolderPath
        {
            get
            {
                return Path.Combine(FolderPath, FolderName);
            }
        }
        public DateTime SavingFileDateTime { get; set; }
        public DateTime CreationDateTime { get; set; }
        public bool IsEditable { get; set; } = true;
        public string? SavedFile { get; set; }
    }
}
