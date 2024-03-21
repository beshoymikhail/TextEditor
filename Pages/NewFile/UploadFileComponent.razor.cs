using Microsoft.AspNetCore.Components;
using Microsoft.AspNetCore.Components.Forms;

namespace TextEditor.Pages.NewFile
{
    public partial class UploadFileComponent
    {
        [Parameter]
        public string fileName { get; set; }
        [Parameter]
        public string Id { get; set; }
        [Parameter]
        public string input_id { get; set; }
        protected override async Task OnAfterRenderAsync(bool firstRender)
        {
            if (firstRender)
            {
                context.uploaded_files = new Dictionary<string, List<IBrowserFile>>
                {
                    { "auxiliaryfile",new List<IBrowserFile>() },
                    { "implementationfile", new List < IBrowserFile>() },
                    { "specificationfile", new List < IBrowserFile>() }
                };
            }
        }
        private void HandleUploadFiles(InputFileChangeEventArgs e)
        {
            foreach (var file in e.GetMultipleFiles())
            {
                if (!context.uploaded_files[input_id].Any(f => f.Name == file.Name && f.Size == file.Size))
                {
                    context.uploaded_files[input_id].Add(file);
                }
            }
        }
        private void HandleDeleteSpecificFile(IBrowserFile file)
        {
            context.uploaded_files[input_id].Remove(file);
        }
        private void DeleteAllUploadedFile()
        {
            context.uploaded_files[input_id].Clear();
        }
    }
}
