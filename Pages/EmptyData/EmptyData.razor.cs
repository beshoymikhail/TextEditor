﻿using ElectronNET.API.Entities;
using ElectronNET.API;
using TextEditor.Model;

namespace TextEditor.Pages.EmptyData
{
    public partial class EmptyData
    {
        private void HandleDeleteThisFile()
        {
            NavigationManager.NavigateTo("/");
        }
        async Task DeleteItemAsync(Structure structure,DocumentationType documentationType)
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
                context.Documentations[documentationType].DocumentationStructures.Remove(structure);
            }
        }
    }
}
