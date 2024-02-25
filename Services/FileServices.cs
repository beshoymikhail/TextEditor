using Microsoft.AspNetCore.Components.Forms;

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
    }
}
