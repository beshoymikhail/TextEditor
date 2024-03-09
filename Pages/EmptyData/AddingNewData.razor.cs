using Microsoft.AspNetCore.Components;
using Microsoft.JSInterop;
using TextEditor.Model;

namespace TextEditor.Pages.EmptyData
{
    public partial class AddingNewData
    {
        [Parameter]
        public int SectionType { get; set; }
        public Function selectfunctiontoinsert { get; set; }
        public Function shownFunctionInScreen { get; set; }
        public List<SelectedFunction> ChoosenFunctions { get; set; } = new List<SelectedFunction>() { };
        public List<SelectedFunction> NewelectedFunction { get; set; }= new List<SelectedFunction>() { };
        protected override async Task OnAfterRenderAsync(bool firstRender)
        {
            if (firstRender)
            {
                SectionType = int.Parse(NavigationManager.Uri.Split("=")[1]);
                ChoosenFunctions = context.SelectedFunctions.Where(sf => sf.SectionType == (SectionType)SectionType).ToList();
                shownFunctionInScreen = ChoosenFunctions.FirstOrDefault();
                StateHasChanged();
            }
        }
        private void HandleInsertFunction()
        {
            if (!ChoosenFunctions.Any(cf => cf.Id == selectfunctiontoinsert.Id))
            {
                SelectedFunction sf = new SelectedFunction
                {
                    Id = selectfunctiontoinsert.Id,
                    Name = selectfunctiontoinsert.Name,
                    Description = selectfunctiontoinsert.Description,
                    FileName = selectfunctiontoinsert.FileName,
                    FunctionType = selectfunctiontoinsert.FunctionType,
                    sourceFile = selectfunctiontoinsert.sourceFile,
                    SectionType = (SectionType)SectionType
                };
                ChoosenFunctions.Add(sf);
                NewelectedFunction.Add(sf);
            }
        }
        private void HandleShownFunctionClickedInScreen(int functionId)
        {
            shownFunctionInScreen = ChoosenFunctions.FirstOrDefault(cf => cf.Id == functionId);
        }
        private void HandleSaveAndAddFunctionsBtn()
        {
            context.SelectedFunctions.AddRange(NewelectedFunction);
            NavigationManager.NavigateTo("/EmptyData");
        }
        private void HandleDiscardChangesBtn()
        {
            ChoosenFunctions = context.SelectedFunctions.Where(sf => sf.SectionType == (SectionType)SectionType).ToList();
            NewelectedFunction.Clear();
            shownFunctionInScreen = ChoosenFunctions.FirstOrDefault();
        }
    }
}
