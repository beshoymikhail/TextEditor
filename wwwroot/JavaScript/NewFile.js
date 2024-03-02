function UploadFile(input) {
    document.getElementById(input).click();
}

function ReplaceFile(InputId) {
    document.getElementById(InputId).click();
}

function DeleteFile(InputId) {
    document.getElementById(InputId).DeleteFile();
}

function renderjQueryComponents() {
    $("#btn-open-existing-file").on('click', function () {''

        $("#open-existing-file").click()
    })
    $("#btn-upload-external-file").on('click', function () {
        $("#external-file").click()
    })
    $("#btn-introduction").on('click', function () {
        $("#input-introduction-text").focus()
    })

}
