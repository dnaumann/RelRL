import * as vscode from 'vscode';
import { spawn } from 'child_process';
import * as path from 'path';

export function activate(context: vscode.ExtensionContext) {
    const diagnosticCollection = vscode.languages.createDiagnosticCollection('whyrel');
    context.subscriptions.push(diagnosticCollection);

    // Register restart command
    const restartCommand = vscode.commands.registerCommand('whyrel.restart', () => {
        diagnosticCollection.clear();
        vscode.workspace.textDocuments.forEach(document => {
            if (document.languageId === 'whyrel') {
                validateDocument(document, diagnosticCollection);
            }
        });
        vscode.window.showInformationMessage('WhyRel extension restarted');
    });



    // Register document change listener
    const onDidChangeDocument = vscode.workspace.onDidChangeTextDocument(event => {
        if (event.document.languageId === 'whyrel') {
            validateDocument(event.document, diagnosticCollection);
        }
    });

    // Register document open listener
    const onDidOpenDocument = vscode.workspace.onDidOpenTextDocument(document => {
        if (document.languageId === 'whyrel') {
            validateDocument(document, diagnosticCollection);
        }
    });

    // Validate all open WhyRel documents
    vscode.workspace.textDocuments.forEach(document => {
        if (document.languageId === 'whyrel') {
            validateDocument(document, diagnosticCollection);
        }
    });

    context.subscriptions.push(restartCommand, onDidChangeDocument, onDidOpenDocument);
}

function validateDocument(document: vscode.TextDocument, diagnosticCollection: vscode.DiagnosticCollection) {
    if (document.uri.scheme !== 'file') {
        return;
    }

    const filePath = document.uri.fsPath;
    const whyrelBinary = getWhyRelBinaryPath();
    
    if (!whyrelBinary) {
        return;
    }

    // Clear existing diagnostics
    diagnosticCollection.delete(document.uri);

    // Run syntax check first
    runSyntaxCheck(whyrelBinary, filePath, document, diagnosticCollection);
}

function runSyntaxCheck(
    whyrelBinary: string,
    filePath: string,
    document: vscode.TextDocument,
    diagnosticCollection: vscode.DiagnosticCollection
) {
    const process = spawn(whyrelBinary, ['-parse', filePath]);
    let stderr = '';

    process.stderr.on('data', (data) => {
        stderr += data.toString();
    });

    process.on('close', (code) => {
        if (code !== 0 && stderr) {
            // Syntax errors found - show them and don't run type check
            const diagnostics = parseWhyRelErrors(stderr, document, 'syntax');
            diagnosticCollection.set(document.uri, diagnostics);
        } else {
            // Syntax is valid - now run type check
            runTypeCheck(whyrelBinary, filePath, document, diagnosticCollection);
        }
    });
}

function runTypeCheck(
    whyrelBinary: string,
    filePath: string,
    document: vscode.TextDocument,
    diagnosticCollection: vscode.DiagnosticCollection
) {
    const process = spawn(whyrelBinary, ['-type-check', filePath]);
    let stderr = '';

    process.stderr.on('data', (data) => {
        stderr += data.toString();
    });

    process.on('close', (code) => {
        if (code !== 0 && stderr) {
            const diagnostics = parseWhyRelErrors(stderr, document, 'type');
            diagnosticCollection.set(document.uri, diagnostics);
        }
    });
}

function parseWhyRelErrors(stderr: string, document: vscode.TextDocument, checkType: 'syntax' | 'type'): vscode.Diagnostic[] {
    const diagnostics: vscode.Diagnostic[] = [];
    const lines = stderr.split('\n');

    for (const line of lines) {
        // Parse error formats:
        // filename:line:column: error message
        // Type error: filename:line:column-column: error message
        const match = line.match(/^(?:Type error: )?([^:]+):(\d+):(\d+)(?:-\d+)?:\s*(.+)$/);
        if (match) {
            const [, , lineStr, columnStr, message] = match;
            const lineNum = parseInt(lineStr) - 1; // VS Code uses 0-based line numbers
            const columnNum = parseInt(columnStr) - 1; // VS Code uses 0-based column numbers

            if (lineNum >= 0 && lineNum < document.lineCount) {
                const line = document.lineAt(lineNum);
                const startPos = new vscode.Position(lineNum, Math.max(0, columnNum));
                // Highlight the word at the error position, or rest of line if no word found
                const wordRange = document.getWordRangeAtPosition(startPos) || 
                    new vscode.Range(startPos, new vscode.Position(lineNum, line.text.length));
                
                const diagnostic = new vscode.Diagnostic(wordRange, message, vscode.DiagnosticSeverity.Error);
                diagnostic.source = checkType === 'syntax' ? 'WhyRel Syntax' : 'WhyRel Type Checker';
                diagnostics.push(diagnostic);
            }
        }
    }

    return diagnostics;
}

function getWhyRelBinaryPath(): string | null {
    // Try to find WhyRel binary
    const config = vscode.workspace.getConfiguration('whyrel');
    const configuredPath = config.get<string>('binaryPath');
    
    if (configuredPath) {
        return configuredPath;
    }

    // Try workspace-relative path
    const workspaceFolders = vscode.workspace.workspaceFolders;
    if (workspaceFolders && workspaceFolders.length > 0) {
        const workspaceRoot = workspaceFolders[0].uri.fsPath;
        const relativePath = path.join(workspaceRoot, 'bin', 'whyrel');
        return relativePath;
    }

    return null;
}

export function deactivate() {}