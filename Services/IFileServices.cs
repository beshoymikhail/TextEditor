using Microsoft.AspNetCore.Components.Forms;
using TextEditor.Model;

namespace TextEditor.Services
{
    public interface IFileServices
    {
        public Task CreatingSavedFile( string folderPath, string folderName);
        public Task CopyFileToFolder(List<IBrowserFile> files, string folderPath);
        public Task<List<Structure>> ExtractFile(List<IBrowserFile> files, SourceFile sourceFile);
    }
}
