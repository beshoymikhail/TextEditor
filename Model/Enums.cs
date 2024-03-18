using System.ComponentModel.DataAnnotations;
namespace TextEditor.Model
{
    public static class EnumExtensions
    {
        public static string GetDisplayName(this Enum value)
        {
            var field = value.GetType().GetField(value.ToString());
            var displayAttribute = (DisplayAttribute)Attribute.GetCustomAttribute(field, typeof(DisplayAttribute));
            return displayAttribute != null ? displayAttribute.Name : value.ToString();
        }
    }
    [AttributeUsage(AttributeTargets.Field)]
    public class DisplayAttribute : Attribute
    {
        public string Name { get; }

        public DisplayAttribute(string name)
        {
            Name = name;
        }
    }
    public enum FunctionType
    {
        Function,
        Lemma,
        Fixpoint,
        Definition,
        Inductive,
        Record,
        Class,
        [Display("Program Definition")]
        ProgramDefinition,
        [Display("Program Fixpoint")]
        ProgramFixpoint,
        Theorems,
        Fact,
        Remark,
        Corollary,
        Proposition,
        Properties,
        Canonical
    }
    public enum SourceFile
    {
        Implementation,
        Specification,
        Auxiliary
    }
    public enum SectionType
    {
        DataTypes,
        AdmittedLemmas,
        MainFunctions,
        SupportFunctions,
        AuxiliaryFunctions,
        OtherRelevantFunctions
    }
}
