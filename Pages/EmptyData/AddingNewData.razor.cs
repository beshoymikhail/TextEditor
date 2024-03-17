using ElectronNET.API.Entities;
using ElectronNET.API;
using Microsoft.AspNetCore.Components;
using Microsoft.JSInterop;
using SocketIOClient.Messages;
using TextEditor.Model;
using TextEditor.Services;
using System.Linq;
using System;

namespace TextEditor.Pages.EmptyData
{
    public partial class AddingNewData
    {
        public SectionType _sectionType;
        public List<string> TabList { get; set; } = new List<string> { "" };
        public List<FunctionType> Panels { get; set; } = new List<FunctionType>();
        public Function selectfunctiontoinsert { get; set; }
        public Function shownFunctionInScreen { get; set; }
        public List<Function> FunctionsInPanels { get; set; } = new List<Function>();
        public List<SelectedFunction> ChoosenFunctions { get; set; } = new List<SelectedFunction>() { };
        public List<SelectedFunction> NewelectedFunction { get; set; } = new List<SelectedFunction>() { };

        protected override async Task OnAfterRenderAsync(bool firstRender)
        {
            if (firstRender)
            {
                _sectionType = (SectionType)int.Parse(NavigationManager.Uri.Split("=")[1]);
                TabList = HelperMethods.GetTabList(_sectionType);
                Panels = HelperMethods.GetFunctionType(_sectionType, TabList[0]);
                var sourcefiles = HelperMethods.GetSourceFiles(_sectionType, TabList[0]);
                FunctionsInPanels = context.functions.Where(f => sourcefiles.Contains(f.sourceFile) && Panels.Contains(f.FunctionType)).ToList();
                ChoosenFunctions = context.SelectedFunctions.Where(sf => sf.SectionType == _sectionType).ToList();
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
                    SectionType = _sectionType
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
            ChoosenFunctions = context.SelectedFunctions.Where(sf => sf.SectionType == _sectionType).ToList();
            NewelectedFunction.Clear();
            shownFunctionInScreen = ChoosenFunctions.FirstOrDefault();
        }
        async Task DeleteItemAsync(SelectedFunction selectedFunction)
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
                ChoosenFunctions.Remove(selectedFunction);
                NewelectedFunction.Remove(selectedFunction);
                shownFunctionInScreen = null;
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
                ChoosenFunctions?.Clear();
                NewelectedFunction?.Clear();
                context.SelectedFunctions.RemoveAll(sf => sf.SectionType == _sectionType);
                shownFunctionInScreen = null;
            }
        }
        private void HandleTabListChange(int tablLlistId)
        {
            selectfunctiontoinsert = null;
            Panels = HelperMethods.GetFunctionType(_sectionType, TabList[tablLlistId]);
            var sourcefiles = HelperMethods.GetSourceFiles(_sectionType, TabList[tablLlistId]);
            FunctionsInPanels = context.functions.Where(f => sourcefiles.Contains(f.sourceFile) && Panels.Contains(f.FunctionType)).ToList();
        }
    }
}
