﻿using Microsoft.AspNetCore.Components.Forms;
using TextEditor.Model;

namespace TextEditor.Services
{
    public interface IFileServices
    {
         public Task CopyFileToFolder(IBrowserFile file, string folderPath);
        public Task<List<Function>> ExtractFile(IBrowserFile file,SourceFile sourceFile);
    }
}
