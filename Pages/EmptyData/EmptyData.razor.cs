using ElectronNET.API.Entities;
using ElectronNET.API;
using System.Text.Json;
using TextEditor.Model;
using TextEditor.Services;

namespace TextEditor.Pages.EmptyData
{
    public partial class EmptyData
    {
        private IFileServices fileServices = new FileServices();
        private void HandleDeleteThisFile()
        {
            NavigationManager.NavigateTo("/");
        }
        private async void HandleSaveFile()
        {
            string jsonString = JsonSerializer.Serialize(
                new
                {
                    Introduction = context.Introduction,
                    SavingFileDateTime = DateTime.Now.ToString(),
                    saved_uploaded_files = context.saved_uploaded_files,
                    Documentations = context.Documentations
                }, new JsonSerializerOptions { WriteIndented = true });
            File.WriteAllText($"{context.FullFolderPath}/{context.FolderName}.fv", jsonString);

        }
    }
}
