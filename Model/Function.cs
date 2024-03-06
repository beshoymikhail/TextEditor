namespace TextEditor.Model
{
    public class Function
    {
        public int Id { get; set; }
        public string Name { get; set; }
        public string Description { get; set; }
        public string FileName { get; set; }
        public FunctionType FunctionType { get; set; }
        public SourceFile sourceFile { get; set; }
    }
}
