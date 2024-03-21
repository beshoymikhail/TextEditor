class GreetingHelpers {
    static dotNetHelper;

    static setDotNetHelper(value) {
        GreetingHelpers.dotNetHelper = value;
    }
}
window.GreetingHelpers = GreetingHelpers;
function UploadFile(InputId) {
    $(`#${InputId}`).click()
}


function renderjQueryComponents() {
    $("#btn-open-existing-file").on('click', function () {
        $("#open-existing-file").click()
    })
    $("#btn-upload-external-file").on('click', function () {
        $("#external-file").click()
    })
    $("#btn-introduction").on('click', function () {
        $("#input-introduction-text").focus()
    })
}