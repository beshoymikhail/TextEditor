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
                dotNetHelper = DotNetObjectReference.Create(this);
                await jsRuntime.InvokeVoidAsync("GreetingHelpers.setDotNetHelper",
                    dotNetHelper);
            }
        }
        public async void HandleUploadAuxiliaryFile(InputFileChangeEventArgs e)
        {
            context.uploaded_files["auxiliaryfile"] = e.File;
            context.functions = await fileServices.ExtractFile(context.uploaded_files["auxiliaryfile"], SourceFile.Implementation);
        }

        private void HandleUploadImplementationFile(InputFileChangeEventArgs e)
        {
            context.uploaded_files["implementationfile"] = e.File;
        }
        private void HandleUploadSpecificationFile(InputFileChangeEventArgs e)
        {
            context.uploaded_files["specificationfile"] = e.File;
        }
        private void HandleCreateProjectBtn()
        {
            if (IsEnabled && !string.IsNullOrEmpty(context.FolderName) && !string.IsNullOrEmpty(context.FolderPath))
            {
                fileServices.CopyFileToFolder(context.uploaded_files["auxiliaryfile"],context.FullFolderPath);
                fileServices.CopyFileToFolder(context.uploaded_files["implementationfile"], context.FullFolderPath);
                fileServices.CopyFileToFolder(context.uploaded_files["specificationfile"], context.FullFolderPath);
                
                //var x2 = fileServices.ExtractFile(uploaded_files["implementationfile"]);
                //var x3 = fileServices.ExtractFile(uploaded_files["specificationfile"]);
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
