using TextEditor.Model;

namespace TextEditor.Data
{
    public class Context
    {
        public List<Function> functions { get; set; }=new List<Function>();
        public List<SelectedFunction> SelectedFunctions { get; set; }=new List<SelectedFunction>();
    }
}
