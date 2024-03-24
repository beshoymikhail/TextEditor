namespace TextEditor.Model
{
    public class Documentation
    {
        public string DocumentationText { get; set; }=string.Empty;
        public List<Structure> DocumentationStructures { get; set; }=new List<Structure>();
    }
}
