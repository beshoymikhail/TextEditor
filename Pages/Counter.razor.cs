namespace TextEditor.Pages
{
    public partial class Counter
    {
        protected int incremntcounter { get; set; } = 1;
        protected void IncrementCount()
        {
            incremntcounter++;
        }
    }
}
