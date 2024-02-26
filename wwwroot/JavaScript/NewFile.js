function UploadFile(input) {
    document.getElementById(input).click();
}

function ReplaceFile(InputId) {
    document.getElementById(InputId).click();
}

function DeleteFile(InputId) {
    document.getElementById(InputId).DeleteFile();
}
$(document).ready(function () {
    $('.nav-link').on('click', function () {
        $('.nav-link').removeClass('active');
        $(this).addClass('active');
    });
})
