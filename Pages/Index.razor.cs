using ElectronNET.API;
using ElectronNET.API.Entities;
using Microsoft.AspNetCore.Components;
using Microsoft.AspNetCore.Components.Forms;
using Newtonsoft.Json;
using TextEditor.Data;
using TextEditor.Model;
using TextEditor.Services;

namespace TextEditor.Pages
{
    public partial class Index
    {
        private IFileServices fileServices = new FileServices();
        protected override async Task OnAfterRenderAsync(bool firstRender)
        {
            context.uploaded_files["auxiliaryfile"] = new List<IBrowserFile>();
            context.uploaded_files["implementationfile"] = new List<IBrowserFile>();
            context.uploaded_files["specificationfile"] = new List<IBrowserFile>();
            context.FolderName = "";
            context.FolderPath = "";
        }
        private async Task HandleLearnMoreButton()
        {
            await Electron.Shell.OpenExternalAsync("https://formalv.com");
        }
        private async Task HandleBtnOpenExistingFile()
        {
            var fileoptions = new OpenDialogOptions
            {
                Filters = new FileFilter[] { new FileFilter { Name = "fv files", Extensions = new string[] { "fv" } } }
            };

            var mainwindow = Electron.WindowManager.BrowserWindows.FirstOrDefault();
            var fileresult = await Electron.Dialog.ShowOpenDialogAsync(mainwindow, fileoptions);

            if (fileresult != null && fileresult.Length > 0)
            {
                string selectedFile = fileresult[0];
                var fileAsString = await fileServices.ReadFileAsString(selectedFile);
                if (string.IsNullOrEmpty(fileAsString))
                {
                    var options = new MessageBoxOptions("The Choosen File is Empty.");
                    options.Buttons = new string[] { "OK" };
                    options.Title = "Alert";
                    options.Type = MessageBoxType.warning;
                    await Electron.Dialog.ShowMessageBoxAsync(options);
                    return;
                }
                context.SavedFile = selectedFile;
                var selectDirectory = Path.GetDirectoryName(selectedFile);
                var fileds = selectDirectory?.Split(@"\").ToList();

                context.FolderName = fileds[fileds.Count - 1];
                context.FolderPath = selectDirectory.Split($@"\{context.FolderName}")[0];
                Console.WriteLine($"Folder name:{context.FolderName}\nFolderPath:{context.FolderPath}\nFullFolderPath:{context.FullFolderPath}");

                var cont = JsonConvert.DeserializeObject<Context>(fileAsString);
                context.saved_uploaded_files = cont.saved_uploaded_files;
                context.Introduction = cont.Introduction;
                context.Documentations = cont.Documentations;
                context.SavingFileDateTime = cont.SavingFileDateTime;
                var files = Directory.GetFiles(context.FullFolderPath);
                foreach (var item in files)
                {
                    Console.WriteLine(item);
                }
                foreach (var item in context.saved_uploaded_files)
                {
                    if (item.Value.Count < 1)
                    {
                        context.IsEditable = false;
                        break;
                    }
                    foreach (var file in item.Value)
                    {
                        context.IsEditable = files.Contains($"{Path.Combine(context.FullFolderPath, file)}");
                        if (!context.IsEditable)
                        {
                            break;
                        }
                    }
                    if (!context.IsEditable)
                    {
                        break;
                    }
                }
                if (context.IsEditable)
                {
                    context.structures = await fileServices.ExtractFile(context.saved_uploaded_files["auxiliaryfile"], SourceFile.Auxiliary, context.FullFolderPath);
                    context.structures.AddRange(await fileServices.ExtractFile(context.saved_uploaded_files["implementationfile"], SourceFile.Implementation, context.FullFolderPath));
                    context.structures.AddRange(await fileServices.ExtractFile(context.saved_uploaded_files["specificationfile"], SourceFile.Specification, context.FullFolderPath));
                    NavigationManager.NavigateTo("/EmptyData");
                }
                else
                {
                    var options = new MessageBoxOptions("It's Not Editable File\nAll recorded files for auxiliary file, implementation file, specification file are not available for the selected folder.");
                    options.Buttons = new string[] { "OK" };
                    options.Title = "Alert";
                    options.Type = MessageBoxType.info;
                    await Electron.Dialog.ShowMessageBoxAsync(options);
                    NavigationManager.NavigateTo("/EmptyData");
                }
            }
        }
        private async void HandleOpenFileTocheckError()
        {
            string selectedFile = @"D:\TextEditor\test2\test2.fv";
            var fileAsString = await fileServices.ReadFileAsString(selectedFile);
            if (string.IsNullOrEmpty(fileAsString))
            {
                Console.WriteLine("File is Empty");
                return;
            }
            context.SavedFile = selectedFile;
            var selectDirectory = Path.GetDirectoryName(selectedFile);
            var fileds = selectDirectory?.Split(@"\").ToList();

            context.FolderName = fileds[fileds.Count - 1];
            context.FolderPath = selectDirectory.Split($@"\{context.FolderName}")[0];
            Console.WriteLine($"Folder name:{context.FolderName}\nFolderPath:{context.FolderPath}\nFullFolderPath:{context.FullFolderPath}");

            var cont = JsonConvert.DeserializeObject<Context>(fileAsString);
            context.saved_uploaded_files = cont.saved_uploaded_files;
            context.Introduction = cont.Introduction;
            context.Documentations = cont.Documentations;
            context.SavingFileDateTime = cont.SavingFileDateTime;
            var files = Directory.GetFiles(context.FullFolderPath);
            foreach (var item in files)
            {
                Console.WriteLine(item);
            }
            foreach (var item in context.saved_uploaded_files)
            {
                if (item.Value.Count < 1)
                {
                    context.IsEditable = false;
                    break;
                }
                foreach (var file in item.Value)
                {
                    context.IsEditable = files.Contains($"{Path.Combine(context.FullFolderPath, file)}");
                    if (!context.IsEditable)
                    {
                        break;
                    }
                }
                if (!context.IsEditable)
                {
                    break;
                }
            }
            if (context.IsEditable)
            {
                context.structures = await fileServices.ExtractFile(context.saved_uploaded_files["auxiliaryfile"], SourceFile.Auxiliary, context.FullFolderPath);
                context.structures.AddRange(await fileServices.ExtractFile(context.saved_uploaded_files["implementationfile"], SourceFile.Implementation, context.FullFolderPath));
                context.structures.AddRange(await fileServices.ExtractFile(context.saved_uploaded_files["specificationfile"], SourceFile.Specification, context.FullFolderPath));
                NavigationManager.NavigateTo("/EmptyData");
            }
            else
            {
                Console.WriteLine("Files not correct");
                NavigationManager.NavigateTo("/EmptyData");
            }
        }
    }
}
