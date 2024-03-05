class GreetingHelpers {
    static dotNetHelper;

    static setDotNetHelper(value) {
        GreetingHelpers.dotNetHelper = value;
    }
}
window.GreetingHelpers = GreetingHelpers;
function UploadFile(input) {
    document.getElementById(input).click();
}

function ReplaceFile(InputId) {
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
window.handleButtonClick = (InputId) => {
    $(`#${InputId}`).prop('value', '');
    return GreetingHelpers.dotNetHelper.invokeMethodAsync('handledeleteaux', InputId);
}; 
