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
        private IDictionary<string, IBrowserFile> uploaded_files { get; set; } = new Dictionary<string, IBrowserFile>
           { { "auxiliaryfile",null }, { "implementationfile", null }, { "specificationfile", null } };
        private string FolderName { get; set; } = "";
        private string FolderPath { get; set; } = "D:\\TextEditor";
        public bool IsEnabled
        {
            get
            {
                return uploaded_files["auxiliaryfile"] != null && uploaded_files["implementationfile"] != null && uploaded_files["specificationfile"] != null ? true : false;
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
            uploaded_files["auxiliaryfile"] = e.File;
            context.functions = await fileServices.ExtractFile(uploaded_files["auxiliaryfile"], SourceFile.Implementation);
        }
        private void HandleUploadImplementationFile(InputFileChangeEventArgs e)
        {
            uploaded_files["implementationfile"] = e.File;
        }
        private void HandleUploadSpecificationFile(InputFileChangeEventArgs e)
        {
            uploaded_files["specificationfile"] = e.File;
        }
        private void HandleCreateProjectBtn()
        {
            if (IsEnabled && !string.IsNullOrEmpty(FolderName) && !string.IsNullOrEmpty(FolderPath))
            {
                var foldername = Path.Combine(FolderPath, FolderName);
                fileServices.CopyFileToFolder(uploaded_files["auxiliaryfile"], foldername);
                fileServices.CopyFileToFolder(uploaded_files["implementationfile"], foldername);
                fileServices.CopyFileToFolder(uploaded_files["specificationfile"], foldername);
                
                //var x2 = fileServices.ExtractFile(uploaded_files["implementationfile"]);
                //var x3 = fileServices.ExtractFile(uploaded_files["specificationfile"]);
                NavigationManager.NavigateTo("/EmptyData");
            }
        }
        [JSInvokable]
        public void handledeleteaux(string fileName)
        {
            uploaded_files[fileName] = null;
            StateHasChanged();
        }
    }
}
