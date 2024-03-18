using ElectronNET.API;
using ElectronNET.API.Entities;
using Microsoft.AspNetCore.Components;
using Microsoft.AspNetCore.Components.Forms;
using Microsoft.JSInterop;
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
                return context.uploaded_files["auxiliaryfile"] != null && context.uploaded_files["implementationfile"] != null && context.uploaded_files["specificationfile"] != null ? true : false;
            }
        }
        private DotNetObjectReference<NewFile>? dotNetHelper;

        protected override async Task OnAfterRenderAsync(bool firstRender)
        {
            if (firstRender)
            {
                context.SelectedFunctions = new List<SelectedFunction>();
                dotNetHelper = DotNetObjectReference.Create(this);
                await jsRuntime.InvokeVoidAsync("GreetingHelpers.setDotNetHelper",
                    dotNetHelper);
            }
        }
        private async void HandleUploadAuxiliaryFile(InputFileChangeEventArgs e)
        {
            context.uploaded_files["auxiliaryfile"] = e.File;
        }

        private async void HandleUploadImplementationFile(InputFileChangeEventArgs e)
        {
            context.uploaded_files["implementationfile"] = e.File;
        }
        private async void HandleUploadSpecificationFile(InputFileChangeEventArgs e)
        {
            context.uploaded_files["specificationfile"] = e.File;

        }
        private async Task HandleCreateProjectBtnAsync()
        {
            if (IsEnabled && !string.IsNullOrEmpty(context.FolderName) && !string.IsNullOrEmpty(context.FolderPath))
            {
                fileServices.CopyFileToFolder(context.uploaded_files["auxiliaryfile"], context.FullFolderPath);
                fileServices.CopyFileToFolder(context.uploaded_files["implementationfile"], context.FullFolderPath);
                fileServices.CopyFileToFolder(context.uploaded_files["specificationfile"], context.FullFolderPath);
                fileServices.CreatingSavedFile(context.FullFolderPath, context.FolderName);
                context.functions = await fileServices.ExtractFile(context.uploaded_files["auxiliaryfile"], SourceFile.Auxiliary);
                context.functions.AddRange(await fileServices.ExtractFile(context.uploaded_files["implementationfile"], SourceFile.Implementation));
                context.functions.AddRange(await fileServices.ExtractFile(context.uploaded_files["specificationfile"], SourceFile.Specification));
                NavigationManager.NavigateTo("/EmptyData");
            }
        }
        [JSInvokable]
        async Task HandleDeleteFile(string fileName)
        {
            context.uploaded_files[fileName] = null;
            StateHasChanged();
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
                // Handle the selected directory path here
                Console.WriteLine("Selected Directory: " + selectedDirectory);
            }
        }
    }
}
