using Microsoft.AspNetCore.Components.Forms;
using TextEditor.Model;

namespace TextEditor.Services
{
    public interface IFileServices
    {
        public Task<string> CreatingSavedFile( string folderPath, string folderName);
        public Task<List<string>> CopyFileToFolder(List<IBrowserFile> files, string folderPath);
        public Task<List<Structure>> ExtractFile(List<string> files, SourceFile sourceFile,string folderPath);
        public string ReadFileAsString(string FilePath);
    }
}
