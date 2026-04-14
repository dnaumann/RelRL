# WhyRel Language Support for VS Code

This extension provides syntax highlighting and real-time type checking for WhyRel (.rl) files.

## Quick Start

**Install the pre-built extension**:
```bash
code --install-extension whyrel-language-support-0.1.0.vsix
```

Then restart VS Code and configure the WhyRel binary path in settings.

## Installation from Source

### Method 1: Install VSIX Package (Recommended)

1. **Create the VSIX package**:
   ```bash
   cd vscode
   npm install
   npm install -g @vscode/vsce
   vsce package --allow-missing-repository
   ```

2. **Install the extension**:
   ```bash
   code --install-extension whyrel-language-support-0.1.0.vsix
   ```

3. **Restart VS Code** to activate the extension

### Method 2: Manual Installation

1. **Copy the compiled extension**:
   ```bash
   cd vscode
   npm install
   npm run compile
   cp -r . ~/.vscode/extensions/whyrel-language-support
   ```

2. **Restart VS Code**

## Configuration

Configure the WhyRel binary path in VS Code settings:

```json
{
  "whyrel.binaryPath": "/path/to/whyrel/bin/whyrel"
}
```

The extension will also look for `bin/whyrel` relative to your workspace root.