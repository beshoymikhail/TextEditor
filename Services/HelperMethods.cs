using TextEditor.Model;

namespace TextEditor.Services
{
    public static class HelperMethods
    {
        public static List<string> GetTabList(SectionType sectionType)
        {
            if (sectionType == SectionType.DataTypes)
            {
               return new List<string> { "Implementaion", "Specification" };
            }
            if (sectionType == SectionType.MainFunctions||sectionType==SectionType.SupportFunctions)
            {
               return new List<string> { "Functions", "Defined by" };
            }
            return new List<string>();
        }
        public static List<FunctionType> GetFunctionType(SectionType sectionType, string Panel)
        {
            if (sectionType==SectionType.DataTypes)
            {
                return new List<FunctionType>
                {
                    FunctionType.Inductive, FunctionType.Record, FunctionType.Definition, FunctionType.Class
                };
            }
            return new List<FunctionType>();
        }
        public static List<SourceFile> GetSourceFiles(SectionType sectionType,string Panel)
        {
            if (sectionType == SectionType.DataTypes && Panel == "Implementaion")
            {
                return new List<SourceFile> { SourceFile.Implementation };
            }
            else if(sectionType == SectionType.DataTypes && Panel == "Specification")
            {
               return new List<SourceFile> { SourceFile.Specification };
            }
            return new List<SourceFile>();
        }
    }
}
