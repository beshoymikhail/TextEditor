using System.Security.Claims;

namespace TextEditor.Pages.EmptyData
{
    public partial class EmptyData
    {
        private void HandleDeleteThisFile()
        {
            NavigationManager.NavigateTo("/");
        }
    }
}
