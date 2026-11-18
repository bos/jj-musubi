//! A template language whose keywords are zero-argument methods of one context type, as the
//! templates of `musubi list` and `musubi status` use them.

use std::path::Path;
use std::path::PathBuf;

use jj_cli::template_builder;
use jj_cli::template_builder::TemplateLanguage;
use jj_cli::template_builder::TemplatePropertyKind;
use jj_cli::template_builder::TemplateSymbolTable;
use jj_cli::template_value::OpaqueTemplateValue;
use jj_cli::template_value::TemplateTypeRegistry;
use jj_cli::templater::BoxedTemplateProperty;
use jj_lib::settings::UserSettings;
use jj_lib::template_parser::TemplateParseResult;

/// jj's template language with the builtin functions and methods, and the keywords added to
/// it, each of which gives a value of the context `C` the template is rendered for.
pub struct KeywordLanguage<C> {
    settings: UserSettings,
    current_dir: PathBuf,
    type_registry: TemplateTypeRegistry,
    symbol_table: TemplateSymbolTable<'static, Self>,
}

impl<C: OpaqueTemplateValue + serde::Serialize> KeywordLanguage<C> {
    /// A language with no keywords yet.
    pub fn new(settings: &UserSettings, current_dir: &Path) -> Self {
        let mut type_registry = template_builder::new_core_type_registry();
        type_registry.register::<C>("Self").serializable();
        let mut symbol_table = TemplateSymbolTable::builtin();
        // Creates `C`'s method table, which the keywords go in and which lookup requires.
        symbol_table.register_methods::<C>();
        Self {
            settings: settings.clone(),
            current_dir: current_dir.to_owned(),
            type_registry,
            symbol_table,
        }
    }

    /// Adds keyword `name`, which `build` turns from the context into a value.
    pub fn add_keyword<F>(&mut self, name: &'static str, build: F)
    where
        F: Fn(
                BoxedTemplateProperty<'static, C>,
            ) -> TemplateParseResult<TemplatePropertyKind<'static>>
            + 'static,
    {
        self.symbol_table.register_methods::<C>().insert(
            name,
            move |_language, _diagnostics, _build_ctx, self_property, function| {
                function.expect_no_arguments()?;
                build(self_property)
            },
        );
    }
}

impl<C: OpaqueTemplateValue + serde::Serialize> TemplateLanguage<'static> for KeywordLanguage<C> {
    fn settings(&self) -> &UserSettings {
        &self.settings
    }

    fn current_dir(&self) -> &Path {
        &self.current_dir
    }

    fn type_registry(&self) -> &TemplateTypeRegistry {
        &self.type_registry
    }

    fn symbol_table(&self) -> &TemplateSymbolTable<'static, Self> {
        &self.symbol_table
    }
}
