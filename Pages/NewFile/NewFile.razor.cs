using ElectronNET.API;
using ElectronNET.API.Entities;
using Microsoft.AspNetCore.Components;
using Microsoft.JSInterop;
using TextEditor.Data;
using TextEditor.Model;
using TextEditor.Services;

namespace TextEditor.Pages.NewFile
{
    public partial class NewFile
    {
        private IFileServices fileServices = new FileServices();
        public bool IsEnabled
        {
            get
            {
                return context.uploaded_files["auxiliaryfile"].Count() > 0 && context.uploaded_files["implementationfile"].Count() > 0 && context.uploaded_files["specificationfile"].Count() > 0 ? true : false;
            }
        }
        private DotNetObjectReference<NewFile>? dotNetHelper;

        protected override async Task OnAfterRenderAsync(bool firstRender)
        {
            if (firstRender)
            {
                dotNetHelper = DotNetObjectReference.Create(this);
                await jsRuntime.InvokeVoidAsync("GreetingHelpers.setDotNetHelper",
                    dotNetHelper);
            }
        }
        private async Task HandleCreateProjectBtnAsync()
        {
            try
            {
                if (IsEnabled && !string.IsNullOrEmpty(context.FolderName) && !string.IsNullOrEmpty(context.FolderPath))
                {
                    context.saved_uploaded_files["auxiliaryfile"] = await fileServices.CopyFileToFolder(context.uploaded_files["auxiliaryfile"], context.FullFolderPath);
                    context.saved_uploaded_files["implementationfile"] = await fileServices.CopyFileToFolder(context.uploaded_files["implementationfile"], context.FullFolderPath);
                    context.saved_uploaded_files["specificationfile"] = await fileServices.CopyFileToFolder(context.uploaded_files["specificationfile"], context.FullFolderPath);
                    context.SavedFile = await fileServices.CreatingSavedFile(context.FullFolderPath, context.FolderName);
                    context.CreationDateTime = DateTime.Now;
                    context.structures = await fileServices.ExtractFile(context.saved_uploaded_files["auxiliaryfile"], SourceFile.Auxiliary, context.FullFolderPath);
                    context.structures.AddRange(await fileServices.ExtractFile(context.saved_uploaded_files["implementationfile"], SourceFile.Implementation, context.FullFolderPath));
                    context.structures.AddRange(await fileServices.ExtractFile(context.saved_uploaded_files["specificationfile"], SourceFile.Specification, context.FullFolderPath));
                    NavigationManager.NavigateTo("/EmptyData");
                }
            }
            catch (Exception ex)
            {
                Console.WriteLine(ex.Message);
            }
        }
        async Task SelectDirectory()
        {
            var options = new OpenDialogOptions
            {
                Properties = new OpenDialogProperty[] { OpenDialogProperty.openDirectory }
            };

            var mainWindow = Electron.WindowManager.BrowserWindows.First();
            var result = await Electron.Dialog.ShowOpenDialogAsync(mainWindow, options);

            if (result != null && result.ToList().Count > 0)
            {
                string selectedDirectory = result[0];
                context.FolderPath = selectedDirectory;
                Console.WriteLine("Selected Directory: " + selectedDirectory);
            }
        }
    }
}
