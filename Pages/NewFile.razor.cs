using Microsoft.AspNetCore.Components;
using Microsoft.AspNetCore.Components.Forms;
using Newtonsoft.Json.Linq;
using TextEditor.Services;

namespace TextEditor.Pages
{
    public partial class NewFile
    {
        private IFileServices fileServices=new FileServices();
        private IBrowserFile auxiliaryfile { get; set; }
        private IBrowserFile implementationfile { get; set; }
        private IBrowserFile specificationfile { get; set; }
        private string FolderName { get; set; } = "";
        private string FolderPath { get; set; } = "D:\\TextEditor";
        [Parameter]
        public bool IsEnabled { get; set; }
        private void HandleUploadAuxiliaryFile(InputFileChangeEventArgs e)
        {
            auxiliaryfile = e.File;
            IsEnabled = auxiliaryfile != null && implementationfile != null && specificationfile != null ? true : false;

        }
        private void HandleUploadImplementationFile(InputFileChangeEventArgs e)
        {
            implementationfile = e.File;
            IsEnabled = auxiliaryfile != null && implementationfile != null && specificationfile != null ? true : false;
        }
        private void HandleUploadSpecificationFile(InputFileChangeEventArgs e)
        {
            specificationfile = e.File;
            IsEnabled = auxiliaryfile != null && implementationfile != null && specificationfile != null ? true : false;
        }
        private void HandleCreateProjectBtn()
        {
            if (IsEnabled && !string.IsNullOrEmpty(FolderName) && !string.IsNullOrEmpty(FolderPath))
            {
                var foldername = Path.Combine(FolderPath, FolderName);
                fileServices.CopyFileToFolder(auxiliaryfile, foldername);
                fileServices.CopyFileToFolder(implementationfile, foldername);
                fileServices.CopyFileToFolder(specificationfile, foldername);
            }

        }
    }
}
