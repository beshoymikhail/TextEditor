using ElectronNET.API.Entities;
using ElectronNET.API;
using TextEditor.Model;

namespace TextEditor.Pages.EmptyData
{
    public partial class EmptyData
    {
        private void HandleDeleteThisFile()
        {
            context.uploaded_files["auxiliaryfile"] = null;
            context.uploaded_files["implementationfile"] = null;
            context.uploaded_files["specificationfile"] = null;
            context.FolderName = "";
            //context.FolderPath = "";
            NavigationManager.NavigateTo("/");
        }
        async Task DeleteItemAsync(SelectedFunction selectedFunction)
        {
            var options = new MessageBoxOptions("Do you want delete this question?")
            {
                Type = MessageBoxType.question,
                Buttons = new[] { "Yes", "No" },
                Title = "Deleting Function"
            };
            var result = await Electron.Dialog.ShowMessageBoxAsync(options);
            if (result.Response == 0)
            {
                context.SelectedFunctions.Remove(selectedFunction);
            }
        }
    }
}
