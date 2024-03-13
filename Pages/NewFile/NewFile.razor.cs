using ElectronNET.API;
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
                context.uploaded_files["auxiliaryfile"] = null;
                context.uploaded_files["implementationfile"] = null;
                context.uploaded_files["specificationfile"] = null;
                dotNetHelper = DotNetObjectReference.Create(this);
                await jsRuntime.InvokeVoidAsync("GreetingHelpers.setDotNetHelper",
                    dotNetHelper);
            }
        }
        public async void HandleUploadAuxiliaryFile(InputFileChangeEventArgs e)
        {
            context.uploaded_files["auxiliaryfile"] = e.File;
        }

        private void HandleUploadImplementationFile(InputFileChangeEventArgs e)
        {
            context.uploaded_files["implementationfile"] = e.File;
        }
        private void HandleUploadSpecificationFile(InputFileChangeEventArgs e)
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
                context.SelectedFunctions = new List<SelectedFunction>();
                context.functions= await fileServices.ExtractFile(context.uploaded_files["auxiliaryfile"], SourceFile.Auxiliary);
                context.functions.AddRange(await fileServices.ExtractFile(context.uploaded_files["implementationfile"], SourceFile.Implementation));
                context.functions.AddRange(await fileServices.ExtractFile(context.uploaded_files["specificationfile"], SourceFile.Specification));
                NavigationManager.NavigateTo("/EmptyData");
            }
        }
        [JSInvokable]
        public void handledeleteaux(string fileName)
        {
            context.uploaded_files[fileName] = null;
            StateHasChanged();
        }

    }
}
