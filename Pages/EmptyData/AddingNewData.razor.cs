using ElectronNET.API.Entities;
using ElectronNET.API;
using Microsoft.AspNetCore.Components;
using TextEditor.Model;
using TextEditor.Services;

namespace TextEditor.Pages.EmptyData
{
    public partial class AddingNewData
    {
        public DocumentationType _documentaionType;
        public List<string> TabList { get; set; } = new List<string> { "" };
        public List<StructureType> Panels { get; set; } = new List<StructureType>();
        public Structure selected_structure_to_insert { get; set; } 
        public int shownStructureInScreenID { get; set; } = 0;
        public List<Structure> StructureInPanels { get; set; } = new List<Structure>();
        public List<Structure> ChoosenStructures { get; set; } = new List<Structure>();
        public List<Structure> NewSelectedStructures { get; set; } = new List<Structure>();
        public int Count_of_panels
        {
            get
            {
                return Panels.Count();
            }
        }
        protected override async Task OnAfterRenderAsync(bool firstRender)
        {
            if (firstRender)
            {
                selected_structure_to_insert = new Structure();
                _documentaionType = (DocumentationType)int.Parse(NavigationManager.Uri.Split("=")[1]);
                TabList = HelperMethods.GetTabList(_documentaionType);
                Panels = HelperMethods.GetStructureType(_documentaionType, TabList[0]);
                var sourcefiles = HelperMethods.GetSourceFiles(_documentaionType, TabList[0]);
                StructureInPanels = context.structures.Where(f => sourcefiles.Contains(f.sourceFile) && Panels.Contains(f.StructureType)).ToList();
                ChoosenStructures = new List<Structure> (context.Documentations[_documentaionType].DocumentationStructures);
                StateHasChanged();
            }
        }
        private void HandleInsertStructure()
        {
            if (!ChoosenStructures.Any(cf => cf.Id == selected_structure_to_insert.Id))
            {
                Structure sf = new Structure
                {
                    Id = selected_structure_to_insert.Id,
                    Name = selected_structure_to_insert.Name,
                    Description = selected_structure_to_insert.Description,
                    StructureType = selected_structure_to_insert.StructureType,
                    sourceFile = selected_structure_to_insert.sourceFile
                };
                NewSelectedStructures.Add(sf);
                ChoosenStructures.Add(sf);
            }
        }
        private void HandleShownStructureClickedInScreen(int StructureId)
        {
            shownStructureInScreenID = (int)(ChoosenStructures?.FirstOrDefault(cf => cf.Id == StructureId).Id);
            StateHasChanged();
        }
        private void HandleBtnSaveAndAddStructures()
        {
            context.Documentations[_documentaionType].DocumentationStructures= ChoosenStructures;
            NavigationManager.NavigateTo("/EmptyData");
        }
        private void HandleDiscardChangesBtn()
        {
            ChoosenStructures = new List<Structure>(context.Documentations[_documentaionType].DocumentationStructures);
            NewSelectedStructures.Clear();
            shownStructureInScreenID = 0;
        }
        async Task DeleteItemAsync(Structure selectedStructure)
        {
            var options = new MessageBoxOptions("Do you want delete this question?")
            {
                Type = MessageBoxType.question,
                Buttons = new[] { "Yes", "No" },
                Title = "Deleting Function"
            };
            var result = await Electron.Dialog.ShowMessageBoxAsync(options);
            if (result.Response == 0)
            {
                ChoosenStructures.Remove(selectedStructure);
                NewSelectedStructures.Remove(selectedStructure);
                shownStructureInScreenID = 0;
            }
        }
        public async Task DeleteAllFunctionsAsync()
        {
            var options = new MessageBoxOptions("Do you want delete this question?")
            {
                Type = MessageBoxType.question,
                Buttons = new[] { "Yes", "No" },
                Title = "Deleting Function"
            };
            var result = await Electron.Dialog.ShowMessageBoxAsync(options);
            if (result.Response == 0)
            {
                ChoosenStructures?.Clear();
                NewSelectedStructures?.Clear();
                shownStructureInScreenID = 0;
            }
        }
        private void HandleTabListChange(int tablLlistId)
        {
            selected_structure_to_insert = null;
            Panels = HelperMethods.GetStructureType(_documentaionType, TabList[tablLlistId]);
            var sourcefiles = HelperMethods.GetSourceFiles(_documentaionType, TabList[tablLlistId]);
            StructureInPanels = context.structures.Where(f => sourcefiles.Contains(f.sourceFile) && Panels.Contains(f.StructureType)).ToList();
        }
    }
}
