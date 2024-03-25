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
        private async Task HandleDeleteThisFileAsync()
        {
            var options = new MessageBoxOptions("Do you want delete saved file")
            {
                Type = MessageBoxType.warning,
                Buttons = new[] { "Yes", "No" },
                Title = "Deleting File"
            };
            var result = await Electron.Dialog.ShowMessageBoxAsync(options);
            if (result.Response == 0)
            {
                File.Delete(context.SavedFile);
                NavigationManager.NavigateTo("/");
            }
        } 
        private async void HandleCloseProgram()
        {
            var options = new MessageBoxOptions("Do you want save changes?")
            {
                Type = MessageBoxType.question,
                Buttons = new[] { "Save", "Cancel","Discard" },
                Title = "Close"
            };
            var result = await Electron.Dialog.ShowMessageBoxAsync(options);
            if (result.Response == 0)
            {
                HandleSaveFile();
                NavigationManager.NavigateTo("/");
            } 
            if (result.Response == 2)
            {
                NavigationManager.NavigateTo("/");
            }
        }
        private void HandleSaveFile()
        {
            context.EditingFileDateTime = DateTime.Now.ToString("dd MMM, yyyy");
            string jsonString = JsonSerializer.Serialize(
                new
                {
                    Introduction = context.Introduction,
                    CreationDateTime=context.CreationDateTime,
                    EditingFileDateTime = context.EditingFileDateTime,
                    saved_uploaded_files = context.saved_uploaded_files,
                    Documentations = context.Documentations
                }, new JsonSerializerOptions { WriteIndented = true });
            File.WriteAllText(context.SavedFile, jsonString);
        }
    }
}
