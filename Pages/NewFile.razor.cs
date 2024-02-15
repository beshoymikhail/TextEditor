using Microsoft.AspNetCore.Components;

namespace TextEditor.Pages
{
    public partial class NewFile
    {
        [Parameter]
        public bool IsFileUploaded { get; set; }
    }
}
