using ElectronNET.API;
using ElectronNET.API.Entities;
using Microsoft.AspNetCore.Components;
using Microsoft.AspNetCore.Components.Web;
using TextEditor.Data;
using TextEditor.Services;
var builder = WebApplication.CreateBuilder(args);

// Add services to the container.
builder.Services.AddRazorPages();
builder.Services.AddServerSideBlazor();
builder.Services.AddSingleton<Context>();
builder.Services.AddSingleton<IFileServices,FileServices>();
builder.Services.AddElectron();

builder.WebHost.UseElectron(args);
if (HybridSupport.IsElectronActive)
{
    // Open the Electron-Window here
    _ = Task.Run(async () =>
    {
        BrowserWindowOptions browserWindowOptions= new BrowserWindowOptions();
        browserWindowOptions.Title = "Formal Vindications";
        browserWindowOptions.Icon = "FV-icon.ico";
        
        var window = await Electron.WindowManager.CreateWindowAsync(browserWindowOptions);
        window.OnClosed += () =>
        {
            Electron.App.Quit();
        };
    });
}

var app = builder.Build();

// Configure the HTTP request pipeline.
if (!app.Environment.IsDevelopment())
{
    app.UseExceptionHandler("/Error");
    // The default HSTS value is 30 days. You may want to change this for production scenarios, see https://aka.ms/aspnetcore-hsts.
    app.UseHsts();
}

app.UseHttpsRedirection();

app.UseStaticFiles();

app.UseRouting();

app.MapBlazorHub();
app.MapFallbackToPage("/_Host");

app.Run();