using Microsoft.AspNetCore.Components.Forms;
using System;
using TextEditor.Model;

namespace TextEditor.Data
{
    public class Context
    {
        public List<Function> functions { get; set; } = new List<Function>();
        public List<SelectedFunction> SelectedFunctions { get; set; } = new List<SelectedFunction>();
        public IDictionary<string, IBrowserFile> uploaded_files { get; set; } = new Dictionary<string, IBrowserFile>
           { { "auxiliaryfile",null }, { "implementationfile", null }, { "specificationfile", null } };
        public string FolderPath { get; set; } = "D:\\TextEditor";
        public string FolderName { get; set; } = "";
        public string FullFolderPath { 
            get
            {
               return Path.Combine(FolderPath, FolderName);
            }
        }
    }   
}
