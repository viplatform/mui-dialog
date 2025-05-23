# @viplatform/fe-vi-dialog

A reusable dialog component for React applications built with Material-UI (MUI).

## Installation

```bash
# Using npm
npm install @viplatform/fe-vi-dialog

# Using yarn
yarn add @viplatform/fe-vi-dialog
```

## Features

- Built with Material-UI (MUI) components
- TypeScript support
- Multiple dialog types:
  - Information
  - Confirmation
  - Input
- Customizable sizes and layouts
- Support for primary, secondary, and tertiary actions
- Responsive design
- Theme customization

## Usage

```tsx
import { ViDialog } from "@viplatform/fe-vi-dialog";
import { MODAL_TYPES, INFORMATION_SUBTYPES } from "@viplatform/fe-vi-dialog";

// Basic Information Dialog
const MyComponent = () => {
  const [open, setOpen] = useState(false);

  return (
    <ViDialog
      type={MODAL_TYPES.INFORMATION}
      subtype={INFORMATION_SUBTYPES.ACKNOWLEDGEMENT}
      open={open}
      onClose={() => setOpen(false)}
      title="Dialog Title"
      description="This is a dialog description"
      actions={{
        primaryCtaTitle: "Confirm",
        onPrimaryCtaClick: () => {
          // Handle primary action
          setOpen(false);
        },
      }}
    >
      {/* Optional content */}
    </ViDialog>
  );
};

// Confirmation Dialog
const ConfirmationExample = () => {
  const [open, setOpen] = useState(false);

  return (
    <ViDialog
      type={MODAL_TYPES.CONFIRMATION}
      subtype="default"
      open={open}
      onClose={() => setOpen(false)}
      title="Confirm Action"
      description="Are you sure you want to proceed?"
      actions={{
        primaryCtaTitle: "Yes, proceed",
        secondaryCtaTitle: "Cancel",
        onPrimaryCtaClick: () => {
          // Handle confirmation
          setOpen(false);
        },
        onSecondaryCtaClick: () => {
          setOpen(false);
        },
      }}
    />
  );
};
```

## Props

### Common Props

| Prop          | Type                  | Required | Description                                       |
| ------------- | --------------------- | -------- | ------------------------------------------------- |
| type          | `MODAL_TYPES`         | Yes      | Type of dialog (INFORMATION, CONFIRMATION, INPUT) |
| subtype       | `string`              | Yes      | Subtype of the dialog                             |
| open          | `boolean`             | Yes      | Controls dialog visibility                        |
| onClose       | `() => void`          | Yes      | Callback when dialog is closed                    |
| title         | `string`              | No       | Dialog title                                      |
| subTitle      | `string \| ReactNode` | No       | Dialog subtitle                                   |
| description   | `string`              | No       | Dialog description                                |
| children      | `ReactNode`           | No       | Additional content                                |
| size          | `ModalSize`           | No       | Dialog size (SMALL, MEDIUM, LARGE, EXTRA_LARGE)   |
| showCloseIcon | `boolean`             | No       | Show close icon (default: true)                   |
| showDivider   | `boolean`             | No       | Show divider (default: true)                      |
| showActions   | `boolean`             | No       | Show action buttons (default: true)               |

### Actions Props

| Prop                   | Type         | Required | Description                           |
| ---------------------- | ------------ | -------- | ------------------------------------- |
| primaryCtaTitle        | `string`     | No       | Primary button text                   |
| secondaryCtaTitle      | `string`     | No       | Secondary button text                 |
| tertiaryCtaTitle       | `string`     | No       | Tertiary button text                  |
| isPrimaryCtaLoading    | `boolean`    | No       | Show loading state for primary button |
| isPrimaryCtaDisabled   | `boolean`    | No       | Disable primary button                |
| isSecondaryCtaDisabled | `boolean`    | No       | Disable secondary button              |
| onPrimaryCtaClick      | `() => void` | No       | Primary button click handler          |
| onSecondaryCtaClick    | `() => void` | No       | Secondary button click handler        |
| onTertiaryCtaClick     | `() => void` | No       | Tertiary button click handler         |

Also supports all the props of Mui Dialog component

## Development

### Local Setup

```bash
# Install dependencies
yarn install

# Build package
yarn build

# Run tests
yarn test

# Run tests with coverage
yarn test:coverage
```

### Local Development with yarn link

To test the package in another project locally:

1. In the `fe-vi-dialog` directory:

```bash
# Build the package
yarn build

# Create a global symlink
yarn link
```

2. In your project directory:

```bash
# Link to the package
yarn link "@viplatform/fe-vi-dialog"
```

3. To unlink when done:

```bash
# In your project directory
yarn unlink "@viplatform/fe-vi-dialog"

# In the fe-vi-dialog directory
yarn unlink
```

Note: After making changes to the package, you'll need to:

1. Rebuild the package (`yarn build`)

## License

© [Virtual Internships](https://github.com/viplatform)
