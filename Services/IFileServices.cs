using Microsoft.AspNetCore.Components.Forms;

namespace TextEditor.Services
{
    public interface IFileServices
    {
         public Task CopyFileToFolder(IBrowserFile file, string folderPath);
    }
}
