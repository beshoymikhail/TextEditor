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

        public async Task<string> ExtractFile(IBrowserFile file)
        {
            string extractedfile = "";
            var stream = file.OpenReadStream();
            using (var reader = new StreamReader(stream))
            {
                extractedfile = await reader.ReadToEndAsync();
            }
            return  extractedfile;
        }
    }
}
